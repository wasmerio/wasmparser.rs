/* Copyright 2017 Mozilla Foundation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use std::cmp::min;
use std::result;
use std::str;
use std::vec::Vec;

use primitives::{FuncType, GlobalType, MemoryImmediate, MemoryType, Operator, TableType, Type};

/// Test if `subtype` is a subtype of `supertype`.
fn is_subtype_supertype(subtype: Type, supertype: Type) -> bool {
    match supertype {
        Type::AnyRef => subtype == Type::AnyRef || subtype == Type::AnyFunc,
        _ => subtype == supertype,
    }
}

struct BlockState {
    return_types: Vec<Type>,
    stack_starts_at: usize,
    jump_to_top: bool,
    is_else_allowed: bool,
    is_dead_code: bool,
    polymorphic_values: Option<usize>,
}

impl BlockState {
    fn is_stack_polymorphic(&self) -> bool {
        self.polymorphic_values.is_some()
    }
}

struct FuncState {
    local_types: Vec<Type>,
    blocks: Vec<BlockState>,
    stack_types: Vec<Type>,
    end_function: bool,
}

impl FuncState {
    fn block_at(&self, depth: usize) -> &BlockState {
        assert!(depth < self.blocks.len());
        &self.blocks[self.blocks.len() - 1 - depth]
    }
    fn last_block(&self) -> &BlockState {
        self.blocks.last().unwrap()
    }
    fn assert_stack_type_at(&self, index: usize, expected: Type) -> bool {
        let stack_starts_at = self.last_block().stack_starts_at;
        if self.last_block().is_stack_polymorphic()
            && stack_starts_at + index >= self.stack_types.len()
        {
            return true;
        }
        assert!(stack_starts_at + index < self.stack_types.len());
        is_subtype_supertype(
            self.stack_types[self.stack_types.len() - 1 - index],
            expected,
        )
    }
    fn assert_block_stack_len(&self, depth: usize, minimal_len: usize) -> bool {
        assert!(depth < self.blocks.len());
        let blocks_end = self.blocks.len();
        let block_offset = blocks_end - 1 - depth;
        for i in block_offset..blocks_end {
            if self.blocks[i].is_stack_polymorphic() {
                return true;
            }
        }
        let block_starts_at = self.blocks[block_offset].stack_starts_at;
        self.stack_types.len() >= block_starts_at + minimal_len
    }
    fn assert_last_block_stack_len_exact(&self, len: usize) -> bool {
        let block_starts_at = self.last_block().stack_starts_at;
        if self.last_block().is_stack_polymorphic() {
            let polymorphic_values = self.last_block().polymorphic_values.unwrap();
            self.stack_types.len() + polymorphic_values <= block_starts_at + len
        } else {
            self.stack_types.len() == block_starts_at + len
        }
    }
    fn remove_frame_stack_types(&mut self, remove_count: usize) {
        if remove_count == 0 {
            return;
        }
        let last_block = self.blocks.last_mut().unwrap();
        if last_block.is_stack_polymorphic() {
            let len = self.stack_types.len();
            let non_polymorphic_len = len - last_block.stack_starts_at;
            let remove_non_polymorphic = min(non_polymorphic_len, remove_count);
            self.stack_types.truncate(len - remove_non_polymorphic);
            let polymorphic_values = last_block.polymorphic_values.unwrap();
            let remove_polymorphic = min(remove_count - remove_non_polymorphic, polymorphic_values);
            last_block.polymorphic_values = Some(polymorphic_values - remove_polymorphic);
        } else {
            assert!(self.stack_types.len() >= last_block.stack_starts_at + remove_count);
            let keep = self.stack_types.len() - remove_count;
            self.stack_types.truncate(keep);
        }
    }
    fn push_block(&mut self, ty: Type, block_type: BlockType) {
        let return_types = match ty {
            Type::EmptyBlockType => Vec::with_capacity(0),
            _ => vec![ty],
        };
        if block_type == BlockType::If {
            self.stack_types.pop();
        }
        let stack_starts_at = self.stack_types.len();
        self.blocks.push(BlockState {
            return_types,
            stack_starts_at,
            jump_to_top: block_type == BlockType::Loop,
            is_else_allowed: block_type == BlockType::If,
            is_dead_code: false,
            polymorphic_values: None,
        });
    }
    fn pop_block(&mut self) {
        assert!(self.blocks.len() > 1);
        let last_block = self.blocks.pop().unwrap();
        if last_block.is_stack_polymorphic() {
            assert!(
                self.stack_types.len()
                    <= last_block.return_types.len() + last_block.stack_starts_at
            );
        } else {
            assert!(
                self.stack_types.len()
                    == last_block.return_types.len() + last_block.stack_starts_at
            );
        }
        let keep = last_block.stack_starts_at;
        self.stack_types.truncate(keep);
        self.stack_types.extend_from_slice(&last_block.return_types);
    }
    fn reset_block(&mut self) {
        assert!(self.last_block().is_else_allowed);
        let last_block = self.blocks.last_mut().unwrap();
        let keep = last_block.stack_starts_at;
        self.stack_types.truncate(keep);
        last_block.is_else_allowed = false;
        last_block.polymorphic_values = None;
    }
    fn change_frame(&mut self, remove_count: usize) {
        self.remove_frame_stack_types(remove_count);
    }
    fn change_frame_with_type(&mut self, remove_count: usize, ty: Type) {
        self.remove_frame_stack_types(remove_count);
        self.stack_types.push(ty);
    }
    fn change_frame_with_types(&mut self, remove_count: usize, new_items: &[Type]) {
        self.remove_frame_stack_types(remove_count);
        if new_items.is_empty() {
            return;
        }
        self.stack_types.extend_from_slice(new_items);
    }
    fn change_frame_to_exact_types_from(&mut self, depth: usize) {
        let types = self.block_at(depth).return_types.clone();
        let last_block = self.blocks.last_mut().unwrap();
        let keep = last_block.stack_starts_at;
        self.stack_types.truncate(keep);
        self.stack_types.extend_from_slice(&types);
        last_block.polymorphic_values = None;
    }
    fn change_frame_after_select(&mut self, ty: Option<Type>) {
        self.remove_frame_stack_types(3);
        if ty.is_none() {
            let last_block = self.blocks.last_mut().unwrap();
            assert!(last_block.is_stack_polymorphic());
            last_block.polymorphic_values = Some(last_block.polymorphic_values.unwrap() + 1);
            return;
        }
        self.stack_types.push(ty.unwrap())
    }
    fn start_dead_code(&mut self) {
        let last_block = self.blocks.last_mut().unwrap();
        let keep = last_block.stack_starts_at;
        self.stack_types.truncate(keep);
        last_block.is_dead_code = true;
        last_block.polymorphic_values = Some(0);
    }
    fn end_function(&mut self) {
        self.end_function = true;
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum BlockType {
    Block,
    Loop,
    If,
}

pub trait WasmModuleResources {
    fn types(&self) -> &[FuncType];
    fn tables(&self) -> &[TableType];
    fn memories(&self) -> &[MemoryType];
    fn globals(&self) -> &[GlobalType];
    fn func_type_indices(&self) -> &[u32];
}

pub enum FunctionEnd {
    No,
    Yes,
}

type OperatorValidatorResult<T> = result::Result<T, &'static str>;

#[derive(Copy, Clone)]
pub struct OperatorValidatorConfig {
    pub enable_threads: bool,
    pub enable_reference_types: bool,
}

pub(crate) const DEFAULT_OPERATOR_VALIDATOR_CONFIG: OperatorValidatorConfig =
    OperatorValidatorConfig {
        enable_threads: false,
        enable_reference_types: false,
    };

pub(crate) struct OperatorValidator {
    func_state: FuncState,
    config: OperatorValidatorConfig,
}

impl OperatorValidator {
    pub fn new(
        func_type: &FuncType,
        locals: &[(u32, Type)],
        config: OperatorValidatorConfig,
    ) -> OperatorValidator {
        let mut local_types = Vec::new();
        local_types.extend_from_slice(&*func_type.params);
        for local in locals {
            for _ in 0..local.0 {
                local_types.push(local.1);
            }
        }

        let mut blocks = Vec::new();
        let mut last_returns = Vec::new();
        last_returns.extend_from_slice(&*func_type.returns);
        blocks.push(BlockState {
            return_types: last_returns,
            stack_starts_at: 0,
            jump_to_top: false,
            is_else_allowed: false,
            is_dead_code: false,
            polymorphic_values: None,
        });

        OperatorValidator {
            func_state: FuncState {
                local_types,
                blocks,
                stack_types: Vec::new(),
                end_function: false,
            },
            config,
        }
    }

    pub fn is_dead_code(&self) -> bool {
        self.func_state.last_block().is_dead_code
    }

    fn check_frame_size(&self, require_count: usize) -> OperatorValidatorResult<()> {
        if !self.func_state.assert_block_stack_len(0, require_count) {
            Err("not enough operands")
        } else {
            Ok(())
        }
    }

    fn check_operands_1(&self, operand: Type) -> OperatorValidatorResult<()> {
        self.check_frame_size(1)?;
        if !self.func_state.assert_stack_type_at(0, operand) {
            return Err("stack operand type mismatch");
        }
        Ok(())
    }

    fn check_operands_2(&self, operand1: Type, operand2: Type) -> OperatorValidatorResult<()> {
        self.check_frame_size(2)?;
        if !self.func_state.assert_stack_type_at(1, operand1) {
            return Err("stack operand type mismatch");
        }
        if !self.func_state.assert_stack_type_at(0, operand2) {
            return Err("stack operand type mismatch");
        }
        Ok(())
    }

    fn check_operands(&self, expected_types: &[Type]) -> OperatorValidatorResult<()> {
        let len = expected_types.len();
        self.check_frame_size(len)?;
        for i in 0..len {
            if !self
                .func_state
                .assert_stack_type_at(len - 1 - i, expected_types[i])
            {
                return Err("stack operand type mismatch");
            }
        }
        Ok(())
    }

    fn check_block_return_types(
        &self,
        block: &BlockState,
        reserve_items: usize,
    ) -> OperatorValidatorResult<()> {
        let len = block.return_types.len();
        for i in 0..len {
            if !self
                .func_state
                .assert_stack_type_at(len - 1 - i + reserve_items, block.return_types[i])
            {
                return Err("stack item type does not match block item type");
            }
        }
        Ok(())
    }

    fn check_block_return(&self) -> OperatorValidatorResult<()> {
        let len = self.func_state.last_block().return_types.len();
        if !self.func_state.assert_last_block_stack_len_exact(len) {
            return Err("stack size does not match block type");
        }
        self.check_block_return_types(self.func_state.last_block(), 0)
    }

    fn check_jump_from_block(
        &self,
        relative_depth: u32,
        reserve_items: usize,
    ) -> OperatorValidatorResult<()> {
        if relative_depth as usize >= self.func_state.blocks.len() {
            return Err("invalid block depth");
        }
        let block = self.func_state.block_at(relative_depth as usize);
        if block.jump_to_top {
            if !self
                .func_state
                .assert_last_block_stack_len_exact(reserve_items)
            {
                return Err("stack size does not match target loop type");
            }
            return Ok(());
        }

        let len = block.return_types.len();
        if !self
            .func_state
            .assert_block_stack_len(0, len + reserve_items)
        {
            return Err("stack size does not match target block type");
        }
        self.check_block_return_types(block, reserve_items)
    }

    fn match_block_return(&self, depth1: u32, depth2: u32) -> OperatorValidatorResult<()> {
        if depth1 as usize >= self.func_state.blocks.len() {
            return Err("invalid block depth");
        }
        if depth2 as usize >= self.func_state.blocks.len() {
            return Err("invalid block depth");
        }
        let block1 = self.func_state.block_at(depth1 as usize);
        let block2 = self.func_state.block_at(depth2 as usize);
        let return_types1 = &block1.return_types;
        let return_types2 = &block2.return_types;
        if block1.jump_to_top || block2.jump_to_top {
            if block1.jump_to_top {
                if !block2.jump_to_top && !return_types2.is_empty() {
                    return Err("block types do not match");
                }
            } else if !return_types1.is_empty() {
                return Err("block types do not match");
            }
        } else if *return_types1 != *return_types2 {
            return Err("block types do not match");
        }
        Ok(())
    }

    fn check_memory_index(
        &self,
        memory_index: u32,
        resources: &WasmModuleResources,
    ) -> OperatorValidatorResult<()> {
        if memory_index as usize >= resources.memories().len() {
            return Err("no liner memories are present");
        }
        Ok(())
    }

    fn check_shared_memory_index(
        &self,
        memory_index: u32,
        resources: &WasmModuleResources,
    ) -> OperatorValidatorResult<()> {
        if memory_index as usize >= resources.memories().len() {
            return Err("no liner memories are present");
        }
        if !resources.memories()[memory_index as usize].shared {
            return Err("atomic accesses require shared memory");
        }
        Ok(())
    }

    fn check_memarg(
        &self,
        memarg: &MemoryImmediate,
        max_align: u32,
        resources: &WasmModuleResources,
    ) -> OperatorValidatorResult<()> {
        self.check_memory_index(0, resources)?;
        let align = memarg.flags;
        if align > max_align {
            return Err("align is required to be at most the number of accessed bytes");
        }
        Ok(())
    }

    fn check_threads_enabled(&self) -> OperatorValidatorResult<()> {
        if !self.config.enable_threads {
            return Err("threads support is not enabled");
        }
        Ok(())
    }

    fn check_reference_types_enabled(&self) -> OperatorValidatorResult<()> {
        if !self.config.enable_reference_types {
            return Err("reference types support is not enabled");
        }
        Ok(())
    }

    fn check_shared_memarg_wo_align(
        &self,
        _: &MemoryImmediate,
        resources: &WasmModuleResources,
    ) -> OperatorValidatorResult<()> {
        self.check_shared_memory_index(0, resources)?;
        Ok(())
    }

    fn check_block_type(&self, ty: Type) -> OperatorValidatorResult<()> {
        match ty {
            Type::EmptyBlockType | Type::I32 | Type::I64 | Type::F32 | Type::F64 => Ok(()),
            _ => Err("invalid block return type"),
        }
    }

    fn check_select(&self) -> OperatorValidatorResult<Option<Type>> {
        self.check_frame_size(3)?;
        let func_state = &self.func_state;
        let last_block = func_state.last_block();
        Ok(if last_block.is_stack_polymorphic() {
            match func_state.stack_types.len() - last_block.stack_starts_at {
                0 => None,
                1 => {
                    self.check_operands_1(Type::I32)?;
                    None
                }
                2 => {
                    self.check_operands_1(Type::I32)?;
                    Some(func_state.stack_types[func_state.stack_types.len() - 2])
                }
                _ => {
                    let ty = func_state.stack_types[func_state.stack_types.len() - 3];
                    self.check_operands_2(ty, Type::I32)?;
                    Some(ty)
                }
            }
        } else {
            let ty = func_state.stack_types[func_state.stack_types.len() - 3];
            self.check_operands_2(ty, Type::I32)?;
            Some(ty)
        })
    }

    pub(crate) fn process_operator(
        &mut self,
        operator: &Operator,
        resources: &WasmModuleResources,
    ) -> OperatorValidatorResult<FunctionEnd> {
        if self.func_state.end_function {
            return Err("unexpected operator");
        }
        match *operator {
            Operator::Unreachable => self.func_state.start_dead_code(),
            Operator::Nop => (),
            Operator::Block { ty } => {
                self.check_block_type(ty)?;
                self.func_state.push_block(ty, BlockType::Block)
            }
            Operator::Loop { ty } => {
                self.check_block_type(ty)?;
                self.func_state.push_block(ty, BlockType::Loop)
            }
            Operator::If { ty } => {
                self.check_block_type(ty)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.push_block(ty, BlockType::If)
            }
            Operator::Else => {
                if !self.func_state.last_block().is_else_allowed {
                    return Err("unexpected else: if block is not started");
                }
                self.check_block_return()?;
                self.func_state.reset_block()
            }
            Operator::End => {
                self.check_block_return()?;
                if self.func_state.blocks.len() == 1 {
                    self.func_state.end_function();
                    return Ok(FunctionEnd::Yes);
                }
                if {
                    let last_block = &self.func_state.last_block();
                    last_block.is_else_allowed && !last_block.return_types.is_empty()
                } {
                    return Err("else is expected: if block has type");
                }
                self.func_state.pop_block()
            }
            Operator::Br { relative_depth } => {
                self.check_jump_from_block(relative_depth, 0)?;
                self.func_state.start_dead_code()
            }
            Operator::BrIf { relative_depth } => {
                self.check_operands_1(Type::I32)?;
                self.check_jump_from_block(relative_depth, 1)?;
                if self.func_state.last_block().is_stack_polymorphic() {
                    self.func_state
                        .change_frame_to_exact_types_from(relative_depth as usize)
                } else {
                    self.func_state.change_frame(1)
                }
            }
            Operator::BrTable { ref table } => {
                self.check_operands_1(Type::I32)?;
                let mut depth0: Option<u32> = None;
                for relative_depth in table {
                    if depth0.is_none() {
                        self.check_jump_from_block(relative_depth, 1)?;
                        depth0 = Some(relative_depth);
                        continue;
                    }
                    self.match_block_return(relative_depth, depth0.unwrap())?;
                }
                self.func_state.start_dead_code()
            }
            Operator::Return => {
                let depth = (self.func_state.blocks.len() - 1) as u32;
                self.check_jump_from_block(depth, 0)?;
                self.func_state.start_dead_code()
            }
            Operator::Call { function_index } => {
                if function_index as usize >= resources.func_type_indices().len() {
                    return Err("function index out of bounds");
                }
                let type_index = resources.func_type_indices()[function_index as usize];
                let ty = &resources.types()[type_index as usize];
                self.check_operands(&ty.params)?;
                self.func_state
                    .change_frame_with_types(ty.params.len(), &ty.returns)
            }
            Operator::CallIndirect { index, table_index } => {
                if table_index as usize >= resources.tables().len() {
                    return Err("table index out of bounds");
                }
                if index as usize >= resources.types().len() {
                    return Err("type index out of bounds");
                }
                let ty = &resources.types()[index as usize];
                let mut types = Vec::with_capacity(ty.params.len() + 1);
                types.extend_from_slice(&ty.params);
                types.push(Type::I32);
                self.check_operands(&types)?;
                self.func_state
                    .change_frame_with_types(ty.params.len() + 1, &ty.returns)
            }
            Operator::Drop => {
                self.check_frame_size(1)?;
                self.func_state.change_frame(1)
            }
            Operator::Select => {
                let ty = self.check_select()?;
                self.func_state.change_frame_after_select(ty)
            }
            Operator::GetLocal { local_index } => {
                if local_index as usize >= self.func_state.local_types.len() {
                    return Err("local index out of bounds");
                }
                let local_type = self.func_state.local_types[local_index as usize];
                self.func_state.change_frame_with_type(0, local_type)
            }
            Operator::SetLocal { local_index } => {
                if local_index as usize >= self.func_state.local_types.len() {
                    return Err("local index out of bounds");
                }
                let local_type = self.func_state.local_types[local_index as usize];
                self.check_operands_1(local_type)?;
                self.func_state.change_frame(1)
            }
            Operator::TeeLocal { local_index } => {
                if local_index as usize >= self.func_state.local_types.len() {
                    return Err("local index out of bounds");
                }
                let local_type = self.func_state.local_types[local_index as usize];
                self.check_operands_1(local_type)?;
                self.func_state.change_frame_with_type(1, local_type)
            }
            Operator::GetGlobal { global_index } => {
                if global_index as usize >= resources.globals().len() {
                    return Err("global index out of bounds");
                }
                let ty = &resources.globals()[global_index as usize];
                self.func_state.change_frame_with_type(0, ty.content_type)
            }
            Operator::SetGlobal { global_index } => {
                if global_index as usize >= resources.globals().len() {
                    return Err("global index out of bounds");
                }
                let ty = &resources.globals()[global_index as usize];
                // FIXME
                //    if !ty.mutable {
                //        return self.create_error("global expected to be mutable");
                //    }
                self.check_operands_1(ty.content_type)?;
                self.func_state.change_frame(1)
            }
            Operator::I32Load { ref memarg } => {
                self.check_memarg(memarg, 2, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I64Load { ref memarg } => {
                self.check_memarg(memarg, 3, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::F32Load { ref memarg } => {
                self.check_memarg(memarg, 2, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::F32)
            }
            Operator::F64Load { ref memarg } => {
                self.check_memarg(memarg, 3, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::F64)
            }
            Operator::I32Load8S { ref memarg } => {
                self.check_memarg(memarg, 0, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I32Load8U { ref memarg } => {
                self.check_memarg(memarg, 0, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I32Load16S { ref memarg } => {
                self.check_memarg(memarg, 1, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I32Load16U { ref memarg } => {
                self.check_memarg(memarg, 1, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I64Load8S { ref memarg } => {
                self.check_memarg(memarg, 0, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::I64Load8U { ref memarg } => {
                self.check_memarg(memarg, 0, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::I64Load16S { ref memarg } => {
                self.check_memarg(memarg, 1, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::I64Load16U { ref memarg } => {
                self.check_memarg(memarg, 1, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::I64Load32S { ref memarg } => {
                self.check_memarg(memarg, 2, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::I64Load32U { ref memarg } => {
                self.check_memarg(memarg, 2, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::I32Store { ref memarg } => {
                self.check_memarg(memarg, 2, resources)?;
                self.check_operands_2(Type::I32, Type::I32)?;
                self.func_state.change_frame(2)
            }
            Operator::I64Store { ref memarg } => {
                self.check_memarg(memarg, 3, resources)?;
                self.check_operands_2(Type::I32, Type::I64)?;
                self.func_state.change_frame(2)
            }
            Operator::F32Store { ref memarg } => {
                self.check_memarg(memarg, 2, resources)?;
                self.check_operands_2(Type::I32, Type::F32)?;
                self.func_state.change_frame(2)
            }
            Operator::F64Store { ref memarg } => {
                self.check_memarg(memarg, 3, resources)?;
                self.check_operands_2(Type::I32, Type::F64)?;
                self.func_state.change_frame(2)
            }
            Operator::I32Store8 { ref memarg } => {
                self.check_memarg(memarg, 0, resources)?;
                self.check_operands_2(Type::I32, Type::I32)?;
                self.func_state.change_frame(2)
            }
            Operator::I32Store16 { ref memarg } => {
                self.check_memarg(memarg, 1, resources)?;
                self.check_operands_2(Type::I32, Type::I32)?;
                self.func_state.change_frame(2)
            }
            Operator::I64Store8 { ref memarg } => {
                self.check_memarg(memarg, 0, resources)?;
                self.check_operands_2(Type::I32, Type::I64)?;
                self.func_state.change_frame(2)
            }
            Operator::I64Store16 { ref memarg } => {
                self.check_memarg(memarg, 1, resources)?;
                self.check_operands_2(Type::I32, Type::I64)?;
                self.func_state.change_frame(2)
            }
            Operator::I64Store32 { ref memarg } => {
                self.check_memarg(memarg, 2, resources)?;
                self.check_operands_2(Type::I32, Type::I64)?;
                self.func_state.change_frame(2)
            }
            Operator::MemorySize {
                reserved: memory_index,
            } => {
                self.check_memory_index(memory_index, resources)?;
                self.func_state.change_frame_with_type(0, Type::I32)
            }
            Operator::MemoryGrow {
                reserved: memory_index,
            } => {
                self.check_memory_index(memory_index, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I32Const { .. } => self.func_state.change_frame_with_type(0, Type::I32),
            Operator::I64Const { .. } => self.func_state.change_frame_with_type(0, Type::I64),
            Operator::F32Const { .. } => self.func_state.change_frame_with_type(0, Type::F32),
            Operator::F64Const { .. } => self.func_state.change_frame_with_type(0, Type::F64),
            Operator::I32Eqz => {
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I32Eq
            | Operator::I32Ne
            | Operator::I32LtS
            | Operator::I32LtU
            | Operator::I32GtS
            | Operator::I32GtU
            | Operator::I32LeS
            | Operator::I32LeU
            | Operator::I32GeS
            | Operator::I32GeU => {
                self.check_operands_2(Type::I32, Type::I32)?;
                self.func_state.change_frame_with_type(2, Type::I32)
            }
            Operator::I64Eqz => {
                self.check_operands_1(Type::I64)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I64Eq
            | Operator::I64Ne
            | Operator::I64LtS
            | Operator::I64LtU
            | Operator::I64GtS
            | Operator::I64GtU
            | Operator::I64LeS
            | Operator::I64LeU
            | Operator::I64GeS
            | Operator::I64GeU => {
                self.check_operands_2(Type::I64, Type::I64)?;
                self.func_state.change_frame_with_type(2, Type::I32)
            }
            Operator::F32Eq
            | Operator::F32Ne
            | Operator::F32Lt
            | Operator::F32Gt
            | Operator::F32Le
            | Operator::F32Ge => {
                self.check_operands_2(Type::F32, Type::F32)?;
                self.func_state.change_frame_with_type(2, Type::I32)
            }
            Operator::F64Eq
            | Operator::F64Ne
            | Operator::F64Lt
            | Operator::F64Gt
            | Operator::F64Le
            | Operator::F64Ge => {
                self.check_operands_2(Type::F64, Type::F64)?;
                self.func_state.change_frame_with_type(2, Type::I32)
            }
            Operator::I32Clz | Operator::I32Ctz | Operator::I32Popcnt => {
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I32Add
            | Operator::I32Sub
            | Operator::I32Mul
            | Operator::I32DivS
            | Operator::I32DivU
            | Operator::I32RemS
            | Operator::I32RemU
            | Operator::I32And
            | Operator::I32Or
            | Operator::I32Xor
            | Operator::I32Shl
            | Operator::I32ShrS
            | Operator::I32ShrU
            | Operator::I32Rotl
            | Operator::I32Rotr => {
                self.check_operands_2(Type::I32, Type::I32)?;
                self.func_state.change_frame_with_type(2, Type::I32)
            }
            Operator::I64Clz | Operator::I64Ctz | Operator::I64Popcnt => {
                self.check_operands_1(Type::I64)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::I64Add
            | Operator::I64Sub
            | Operator::I64Mul
            | Operator::I64DivS
            | Operator::I64DivU
            | Operator::I64RemS
            | Operator::I64RemU
            | Operator::I64And
            | Operator::I64Or
            | Operator::I64Xor
            | Operator::I64Shl
            | Operator::I64ShrS
            | Operator::I64ShrU
            | Operator::I64Rotl
            | Operator::I64Rotr => {
                self.check_operands_2(Type::I64, Type::I64)?;
                self.func_state.change_frame_with_type(2, Type::I64)
            }
            Operator::F32Abs
            | Operator::F32Neg
            | Operator::F32Ceil
            | Operator::F32Floor
            | Operator::F32Trunc
            | Operator::F32Nearest
            | Operator::F32Sqrt => {
                self.check_operands_1(Type::F32)?;
                self.func_state.change_frame_with_type(1, Type::F32)
            }
            Operator::F32Add
            | Operator::F32Sub
            | Operator::F32Mul
            | Operator::F32Div
            | Operator::F32Min
            | Operator::F32Max
            | Operator::F32Copysign => {
                self.check_operands_2(Type::F32, Type::F32)?;
                self.func_state.change_frame_with_type(2, Type::F32)
            }
            Operator::F64Abs
            | Operator::F64Neg
            | Operator::F64Ceil
            | Operator::F64Floor
            | Operator::F64Trunc
            | Operator::F64Nearest
            | Operator::F64Sqrt => {
                self.check_operands_1(Type::F64)?;
                self.func_state.change_frame_with_type(1, Type::F64)
            }
            Operator::F64Add
            | Operator::F64Sub
            | Operator::F64Mul
            | Operator::F64Div
            | Operator::F64Min
            | Operator::F64Max
            | Operator::F64Copysign => {
                self.check_operands_2(Type::F64, Type::F64)?;
                self.func_state.change_frame_with_type(2, Type::F64)
            }
            Operator::I32WrapI64 => {
                self.check_operands_1(Type::I64)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I32TruncSF32 | Operator::I32TruncUF32 => {
                self.check_operands_1(Type::F32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I32TruncSF64 | Operator::I32TruncUF64 => {
                self.check_operands_1(Type::F64)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I64ExtendSI32 | Operator::I64ExtendUI32 => {
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::I64TruncSF32 | Operator::I64TruncUF32 => {
                self.check_operands_1(Type::F32)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::I64TruncSF64 | Operator::I64TruncUF64 => {
                self.check_operands_1(Type::F64)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::F32ConvertSI32 | Operator::F32ConvertUI32 => {
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::F32)
            }
            Operator::F32ConvertSI64 | Operator::F32ConvertUI64 => {
                self.check_operands_1(Type::I64)?;
                self.func_state.change_frame_with_type(1, Type::F32)
            }
            Operator::F32DemoteF64 => {
                self.check_operands_1(Type::F64)?;
                self.func_state.change_frame_with_type(1, Type::F32)
            }
            Operator::F64ConvertSI32 | Operator::F64ConvertUI32 => {
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::F64)
            }
            Operator::F64ConvertSI64 | Operator::F64ConvertUI64 => {
                self.check_operands_1(Type::I64)?;
                self.func_state.change_frame_with_type(1, Type::F64)
            }
            Operator::F64PromoteF32 => {
                self.check_operands_1(Type::F32)?;
                self.func_state.change_frame_with_type(1, Type::F64)
            }
            Operator::I32ReinterpretF32 => {
                self.check_operands_1(Type::F32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I64ReinterpretF64 => {
                self.check_operands_1(Type::F64)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::F32ReinterpretI32 => {
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::F32)
            }
            Operator::F64ReinterpretI64 => {
                self.check_operands_1(Type::I64)?;
                self.func_state.change_frame_with_type(1, Type::F64)
            }
            Operator::I32TruncSSatF32 | Operator::I32TruncUSatF32 => {
                self.check_operands_1(Type::F32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I32TruncSSatF64 | Operator::I32TruncUSatF64 => {
                self.check_operands_1(Type::F64)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I64TruncSSatF32 | Operator::I64TruncUSatF32 => {
                self.check_operands_1(Type::F32)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::I64TruncSSatF64 | Operator::I64TruncUSatF64 => {
                self.check_operands_1(Type::F64)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::I32Extend16S | Operator::I32Extend8S => {
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }

            Operator::I64Extend32S | Operator::I64Extend16S | Operator::I64Extend8S => {
                self.check_operands_1(Type::I64)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }

            Operator::I32AtomicLoad { ref memarg }
            | Operator::I32AtomicLoad16U { ref memarg }
            | Operator::I32AtomicLoad8U { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I32)
            }
            Operator::I64AtomicLoad { ref memarg }
            | Operator::I64AtomicLoad32U { ref memarg }
            | Operator::I64AtomicLoad16U { ref memarg }
            | Operator::I64AtomicLoad8U { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands_1(Type::I32)?;
                self.func_state.change_frame_with_type(1, Type::I64)
            }
            Operator::I32AtomicStore { ref memarg }
            | Operator::I32AtomicStore16 { ref memarg }
            | Operator::I32AtomicStore8 { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands_2(Type::I32, Type::I32)?;
                self.func_state.change_frame(2)
            }
            Operator::I64AtomicStore { ref memarg }
            | Operator::I64AtomicStore32 { ref memarg }
            | Operator::I64AtomicStore16 { ref memarg }
            | Operator::I64AtomicStore8 { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands_2(Type::I32, Type::I64)?;
                self.func_state.change_frame(2)
            }
            Operator::I32AtomicRmwAdd { ref memarg }
            | Operator::I32AtomicRmwSub { ref memarg }
            | Operator::I32AtomicRmwAnd { ref memarg }
            | Operator::I32AtomicRmwOr { ref memarg }
            | Operator::I32AtomicRmwXor { ref memarg }
            | Operator::I32AtomicRmw16UAdd { ref memarg }
            | Operator::I32AtomicRmw16USub { ref memarg }
            | Operator::I32AtomicRmw16UAnd { ref memarg }
            | Operator::I32AtomicRmw16UOr { ref memarg }
            | Operator::I32AtomicRmw16UXor { ref memarg }
            | Operator::I32AtomicRmw8UAdd { ref memarg }
            | Operator::I32AtomicRmw8USub { ref memarg }
            | Operator::I32AtomicRmw8UAnd { ref memarg }
            | Operator::I32AtomicRmw8UOr { ref memarg }
            | Operator::I32AtomicRmw8UXor { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands_2(Type::I32, Type::I32)?;
                self.func_state.change_frame_with_type(2, Type::I32)
            }
            Operator::I64AtomicRmwAdd { ref memarg }
            | Operator::I64AtomicRmwSub { ref memarg }
            | Operator::I64AtomicRmwAnd { ref memarg }
            | Operator::I64AtomicRmwOr { ref memarg }
            | Operator::I64AtomicRmwXor { ref memarg }
            | Operator::I64AtomicRmw32UAdd { ref memarg }
            | Operator::I64AtomicRmw32USub { ref memarg }
            | Operator::I64AtomicRmw32UAnd { ref memarg }
            | Operator::I64AtomicRmw32UOr { ref memarg }
            | Operator::I64AtomicRmw32UXor { ref memarg }
            | Operator::I64AtomicRmw16UAdd { ref memarg }
            | Operator::I64AtomicRmw16USub { ref memarg }
            | Operator::I64AtomicRmw16UAnd { ref memarg }
            | Operator::I64AtomicRmw16UOr { ref memarg }
            | Operator::I64AtomicRmw16UXor { ref memarg }
            | Operator::I64AtomicRmw8UAdd { ref memarg }
            | Operator::I64AtomicRmw8USub { ref memarg }
            | Operator::I64AtomicRmw8UAnd { ref memarg }
            | Operator::I64AtomicRmw8UOr { ref memarg }
            | Operator::I64AtomicRmw8UXor { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands_2(Type::I32, Type::I64)?;
                self.func_state.change_frame_with_type(2, Type::I64)
            }
            Operator::I32AtomicRmwXchg { ref memarg }
            | Operator::I32AtomicRmw16UXchg { ref memarg }
            | Operator::I32AtomicRmw8UXchg { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands_2(Type::I32, Type::I32)?;
                self.func_state.change_frame_with_type(2, Type::I32)
            }
            Operator::I32AtomicRmwCmpxchg { ref memarg }
            | Operator::I32AtomicRmw16UCmpxchg { ref memarg }
            | Operator::I32AtomicRmw8UCmpxchg { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands(&[Type::I32, Type::I32, Type::I32])?;
                self.func_state.change_frame_with_type(3, Type::I32)
            }
            Operator::I64AtomicRmwXchg { ref memarg }
            | Operator::I64AtomicRmw32UXchg { ref memarg }
            | Operator::I64AtomicRmw16UXchg { ref memarg }
            | Operator::I64AtomicRmw8UXchg { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands_2(Type::I32, Type::I64)?;
                self.func_state.change_frame_with_type(2, Type::I64)
            }
            Operator::I64AtomicRmwCmpxchg { ref memarg }
            | Operator::I64AtomicRmw32UCmpxchg { ref memarg }
            | Operator::I64AtomicRmw16UCmpxchg { ref memarg }
            | Operator::I64AtomicRmw8UCmpxchg { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands(&[Type::I32, Type::I64, Type::I64])?;
                self.func_state.change_frame_with_type(3, Type::I64)
            }
            Operator::Wake { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands_2(Type::I32, Type::I32)?;
                self.func_state.change_frame_with_type(2, Type::I32)
            }
            Operator::I32Wait { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands(&[Type::I32, Type::I32, Type::I64])?;
                self.func_state.change_frame_with_type(3, Type::I32)
            }
            Operator::I64Wait { ref memarg } => {
                self.check_threads_enabled()?;
                self.check_shared_memarg_wo_align(memarg, resources)?;
                self.check_operands(&[Type::I32, Type::I64, Type::I64])?;
                self.func_state.change_frame_with_type(3, Type::I32)
            }
            Operator::RefNull => {
                self.check_reference_types_enabled()?;
                self.func_state.change_frame_with_type(0, Type::AnyRef)
            }
            Operator::RefIsNull => {
                self.check_reference_types_enabled()?;
                self.check_operands(&[Type::AnyRef])?;
                self.func_state.change_frame_with_type(0, Type::I32)
            }
        }
        Ok(FunctionEnd::No)
    }

    pub(crate) fn process_end_function(&self) -> OperatorValidatorResult<()> {
        if !self.func_state.end_function {
            return Err("expected end of function");
        }
        Ok(())
    }
}
