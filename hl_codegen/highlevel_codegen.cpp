// Copyright (c) 2021-2024, David H. Hovemeyer <david.hovemeyer@gmail.com>
//
// Permission is hereby granted, free of charge, to any person obtaining a
// copy of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation
// the rights to use, copy, modify, merge, publish, distribute, sublicense,
// and/or sell copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
// OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.

#include <cassert>
#include "node.h"
#include "instruction.h"
#include "highlevel.h"
#include "ast.h"
#include "parse.tab.h"
#include "grammar_symbols.h"
#include "exceptions.h"
#include "local_storage_allocation.h"
#include "highlevel_codegen.h"

#include <complex>


// Adjust an opcode for a basic type
HighLevelOpcode get_opcode(HighLevelOpcode base_opcode, std::shared_ptr<Type> type) {
  if (type->is_basic())
    return static_cast<HighLevelOpcode>(int(base_opcode) + int(type->get_basic_type_kind()));
  else if (type->is_pointer())
    return static_cast<HighLevelOpcode>(int(base_opcode) + int(BasicTypeKind::LONG));
  else
    RuntimeError::raise("attempt to use type '%s' as data in opcode selection", type->as_str().c_str());
}

HighLevelCodegen::HighLevelCodegen(const Options &options, int next_label_num)
  : m_options(options)
  , m_next_label_num(next_label_num)
{
}

HighLevelCodegen::~HighLevelCodegen() {
}

void HighLevelCodegen::generate(std::shared_ptr<Function> function) {
  assert(function->get_funcdef_ast() != nullptr);
  assert(!function->get_hl_iseq());

  // Create empty InstructionSequence to hold high-level instructions
  std::shared_ptr<InstructionSequence> hl_iseq(new InstructionSequence());
  function->set_hl_iseq(hl_iseq);

  // Member functions can use m_function to access the Function object
  m_function = function;
  m_next_vreg = function->get_next_reg();

  // Visit function definition
  visit(function->get_funcdef_ast());
}

void HighLevelCodegen::visit_function_definition(Node *n) {
  // generate the name of the label that return instructions should target
  std::string fn_name = n->get_kid(1)->get_str();
  m_return_label_name = ".L" + fn_name + "_return";

  unsigned total_local_storage = 0U;
  total_local_storage = n->get_symbol()->get_offset();

  get_hl_iseq()->append(new Instruction(HINS_enter, Operand(Operand::IMM_IVAL, total_local_storage)));

  // visit body
  visit(n->get_kid(3));

  get_hl_iseq()->define_label(m_return_label_name);
  get_hl_iseq()->append(new Instruction(HINS_leave, Operand(Operand::IMM_IVAL, total_local_storage)));
  get_hl_iseq()->append(new Instruction(HINS_ret));
}

void HighLevelCodegen::visit_statement_list(Node *n) {
  for (auto it = n->cbegin(); it != n->cend(); ++it) {
    visit(*it);
  }
}

void HighLevelCodegen::visit_expression_statement(Node *n) {
  for (auto it = n->cbegin(); it != n->cend(); ++it) {
    visit(*it);
  }
}

void HighLevelCodegen::visit_return_statement(Node *n) {
  get_hl_iseq()->append(new Instruction(HINS_jmp, Operand(Operand::LABEL, m_return_label_name)));
}

void HighLevelCodegen::visit_return_expression_statement(Node *n) {
  Node *expr = n->get_kid(0);

  // generate code to evaluate the expression
  visit(expr);

  // move the computed value to the return value vreg
  HighLevelOpcode mov_opcode = get_opcode(HINS_mov_b, expr->get_type());
  get_hl_iseq()->append(new Instruction(mov_opcode, Operand(Operand::VREG, LocalStorageAllocation::VREG_RETVAL), expr->get_operand()));

  // jump to the return label
  visit_return_statement(n);
}

void HighLevelCodegen::visit_while_statement(Node *n) {
  // 生成循环开始和结束标签
  std::string start_label = next_label();
  std::string end_label = next_label();

  // 定义循环开始标签
  get_hl_iseq()->define_label(start_label);

  // 生成条件表达式的指令
  Node *cond_expr = n->get_kid(0);
  visit(cond_expr);

  // 条件跳转指令：如果条件为假，跳转到 end_label
  get_hl_iseq()->append(new Instruction(HINS_cjmp_f, Operand(cond_expr->get_operand()), Operand(Operand::LABEL, end_label)));

  // 生成循环体指令
  Node *body = n->get_kid(1);
  visit(body);

  // 跳转回循环开始处，继续条件检查
  get_hl_iseq()->append(new Instruction(HINS_jmp, Operand(Operand::LABEL, start_label)));

  // 定义循环结束标签
  get_hl_iseq()->define_label(end_label);
}

void HighLevelCodegen::visit_do_while_statement(Node *n) {
  // 生成循环开始和结束标签
  std::string start_label = next_label();

  // 定义循环开始标签
  get_hl_iseq()->define_label(start_label);

  // 生成循环体指令
  Node *body = n->get_kid(0);
  visit(body);

  // 生成条件表达式的指令
  Node *cond_expr = n->get_kid(1);
  visit(cond_expr);

  // 条件跳转指令：如果条件为真，跳转回 start_label
  get_hl_iseq()->append(new Instruction(HINS_cjmp_t, Operand(cond_expr->get_operand()), Operand(Operand::LABEL, start_label)));

}

void HighLevelCodegen::visit_for_statement(Node *n) {
  // 创建标签
  std::string body_label = next_label();
  std::string cond_label = next_label();

  Node *init_expr = n->get_kid(0);  // 初始化表达式节点
  if (init_expr) {
    visit(init_expr);  // 生成初始化表达式的指令
  }

  get_hl_iseq()->append(new Instruction(HINS_jmp, Operand(Operand::LABEL, cond_label)));

  get_hl_iseq()->define_label(body_label);
  Node *body = n->get_kid(3);  // 循环体节点
  visit(body);  // 生成循环体的指令

  Node *inc_expr = n->get_kid(2);  // 增量表达式节点
  if (inc_expr) {
    visit(inc_expr);  // 增量表达式的指令
  }

  get_hl_iseq()->define_label(cond_label);

  Node *cond_expr = n->get_kid(1);  // 条件表达式节点
  if (cond_expr) {
    visit(cond_expr);  // 生成条件表达式的指令
    get_hl_iseq()->append(new Instruction(HINS_cjmp_t, Operand(cond_expr->get_operand()), Operand(Operand::LABEL, body_label)));
  }
}

void HighLevelCodegen::visit_if_statement(Node *n) {
  Node *cond_expr = n->get_kid(0);
  visit(cond_expr);

  // 生成一个唯一的标签，用于条件为假时跳转
  std::string end_label = next_label();

  // 条件跳转指令：如果条件为假，跳转到 end_label
  get_hl_iseq()->append(new Instruction(HINS_cjmp_f, Operand(cond_expr->get_operand()), Operand(Operand::LABEL, end_label)));

  // 定义 end_label
  get_hl_iseq()->define_label(end_label);
}

void HighLevelCodegen::visit_if_else_statement(Node *n) {
  // 生成条件表达式的指令
  Node *cond_expr = n->get_kid(0);
  visit(cond_expr);

  // 生成两个唯一的标签：else_label 和 end_label
  std::string end_label = next_label();
  std::string else_label = next_label();

  // 条件跳转指令：如果条件为假，跳转到 else_label
  get_hl_iseq()->append(new Instruction(HINS_cjmp_f, Operand(cond_expr->get_operand()), Operand(Operand::LABEL, else_label)));

  // 生成 then 语句块的指令
  Node *then_block = n->get_kid(1);
  visit(then_block);

  // 跳转到 end_label，表示 then 块结束后直接跳过 else
  get_hl_iseq()->append(new Instruction(HINS_jmp, Operand(Operand::LABEL, end_label)));

  // 定义 else_label
  get_hl_iseq()->define_label(else_label);

  // 生成 else 语句块的指令
  Node *else_block = n->get_kid(2);
  visit(else_block);

  // 定义 end_label
  get_hl_iseq()->define_label(end_label);
}

void HighLevelCodegen::visit_binary_expression(Node *n) {
  Node *left = n->get_kid(1);
  Node *right = n->get_kid(2);


  HighLevelOpcode base_opcode;
  switch (n->get_kid(0)->get_tag()) {
    case TOK_PLUS:    base_opcode = HINS_add_b; break;
    case TOK_MINUS:   base_opcode = HINS_sub_b; break;
    case TOK_ASTERISK: base_opcode = HINS_mul_b; break;
    case TOK_DIVIDE:  base_opcode = HINS_div_b; break;
    case TOK_MOD:     base_opcode = HINS_mod_b; break;

    case TOK_EQUALITY:  base_opcode = HINS_cmpeq_b; break;
    case TOK_INEQUALITY: base_opcode = HINS_cmpneq_b; break;
    case TOK_LT:         base_opcode = HINS_cmplt_b; break;
    case TOK_GT:         base_opcode = HINS_cmpgt_b; break;
    case TOK_LTE:        base_opcode = HINS_cmplte_b; break;
    case TOK_GTE:        base_opcode = HINS_cmpgte_b; break;

    case TOK_LOGICAL_AND:base_opcode = HINS_and_b; break;
    case TOK_LOGICAL_OR: base_opcode = HINS_or_b; break;
    case TOK_ASSIGN:     base_opcode = HINS_mov_b; break;

    default:
      RuntimeError::raise("Unsupported binary operation in binary expression");
  }

  HighLevelOpcode opcode = get_typed_opcode(base_opcode, left->get_type());

  if (n->get_kid(0)->get_tag() != TOK_ASSIGN) {
    visit(left);
    visit(right);
    Operand dest(Operand::VREG, get_next_vreg());
    get_hl_iseq()->append(new Instruction(opcode, dest, left->get_operand(), right->get_operand()));
    n->set_operand(dest);
  } else {
    visit(right);
    visit(left);
    get_hl_iseq()->append(new Instruction(opcode, left->get_operand(), right->get_operand()));
  }
}


void HighLevelCodegen::visit_unary_expression(Node *n) {
  Node *operand_node = n->get_kid(0);

  // 生成操作数的指令
  visit(operand_node);

  // 根据操作符的 tag 属性选择适当的基础操作码
  HighLevelOpcode base_opcode;
  switch (n->get_tag()) {
    case TOK_MINUS:      base_opcode = HINS_neg_b; break;     // 取负
    case TOK_NOT:        base_opcode = HINS_not_b; break;     // 按位取反
    case TOK_AMPERSAND:  base_opcode = HINS_localaddr; break; // 取地址
    case TOK_ASTERISK:   base_opcode = HINS_mov_b; break;
    default:
      RuntimeError::raise("Unsupported unary operation in unary expression");
  }

  // 获取适合操作数类型的最终操作码
  HighLevelOpcode opcode = get_typed_opcode(base_opcode, n->get_type());

  // 使用 get_next_vreg 分配一个新的虚拟寄存器
  Operand dest(Operand::VREG, get_next_vreg());

  // 生成一元操作指令
  get_hl_iseq()->append(new Instruction(opcode, dest, operand_node->get_operand()));

  // 将结果操作数保存到节点中以备后续使用
  n->set_operand(dest);
}

void HighLevelCodegen::visit_function_call_expression(Node *n) {
  // 获取函数名称和参数列表
  Node *function_name_node = n->get_kid(0);
  std::string function_name = function_name_node->get_kid(0)->get_str();
  Node *args_list = n->get_kid(1);

  // 遍历参数表达式并生成代码
  int arg_reg = 1;  // 参数寄存器从 vr1 开始
  for (auto it = args_list->cbegin(); it != args_list->cend(); it++) {
    Node *arg = *it;
    // 生成每个参数的代码
    visit(arg);

    // 将参数值放入适当的虚拟寄存器中（vr1 到 vr9）
    Operand arg_dest(Operand::VREG, arg_reg++);
    HighLevelOpcode mov_opcode = get_typed_opcode(HINS_mov_b, arg->get_type());

    // 将参数值从计算结果移动到参数寄存器
    get_hl_iseq()->append(new Instruction(mov_opcode, arg_dest, arg->get_operand()));
  }

  // 生成函数调用指令，目标是函数标签
  Operand func_label(Operand::LABEL, function_name);
  get_hl_iseq()->append(new Instruction(HINS_call, func_label));

  // 函数的返回值存储在 vr0 中
  Operand ret_val(Operand::VREG, LocalStorageAllocation::VREG_RETVAL);

  // 将返回值存储在当前节点中
  n->set_operand(ret_val);
}


void HighLevelCodegen::visit_field_ref_expression(Node *n) {
  // 递归访问基节点，生成基地址的操作数
  Node *base_node = n->get_kid(0);
  visit(base_node);

  // 获取基地址操作数
  Operand base_addr(Operand::VREG, base_node->get_operand().get_base_reg());

  // 从类型信息中查找字段的偏移量
  auto base_type = base_node->get_type();
  std::string field_name = n->get_kid(1)->get_str();
  int field_offset = base_type->get_field_offset(field_name);

  // 计算字段地址：基地址寄存器 + 字段偏移量
  Operand field_addr(Operand::VREG, get_next_vreg());
  get_hl_iseq()->append(new Instruction(HINS_add_l, field_addr, base_addr, Operand(Operand::IMM_IVAL, field_offset)));

  // 将字段地址作为结果存储到节点中
  Operand field_operand(Operand::VREG_MEM, field_addr.get_base_reg());
  n->set_operand(field_operand);
}

void HighLevelCodegen::visit_indirect_field_ref_expression(Node *n) {
  // 递归访问指针的基节点，生成指针基地址的操作数
  Node *base_node = n->get_kid(0);
  visit(base_node);

  // 获取指针基地址操作数
  Operand ptr_base = base_node->get_operand();

  // 从类型信息获取结构体基类型和字段偏移量
  auto base_type = base_node->get_type()->get_base_type();
  std::string field_name = n->get_kid(1)->get_str();
  int field_offset = base_type->get_field_offset(field_name);

  // 计算字段地址：指针基地址 + 字段偏移量
  Operand field_addr(Operand::VREG, get_next_vreg());
  get_hl_iseq()->append(new Instruction(
      HINS_add_l, field_addr, ptr_base, Operand(Operand::IMM_IVAL, field_offset)));

  // 设置当前操作数为 VREGMEM，表示该地址是内存访问
  Operand field_operand(Operand::VREG_MEM, field_addr.get_base_reg());
  n->set_operand(field_operand);
}

void HighLevelCodegen::visit_array_element_ref_expression(Node *n) {
  // 获取数组的基地址
  Node *array_node = n->get_kid(0);
  visit(array_node);

  // 获取索引表达式
  Node *index_node = n->get_kid(1);
  visit(index_node);

  // 获取数组元素大小（假设 n 包含元素类型信息）
  int elem_size = array_node->get_type()->get_base_type()->get_storage_size();

  // 生成基地址的局部偏移（使用 localaddr）
  Operand array_base = array_node->get_operand(); // 数组基地址的操作数
  Operand base_offset(Operand::VREG, get_next_vreg()); // 临时寄存器
  get_hl_iseq()->append(new Instruction(
      HINS_localaddr, base_offset, Operand(Operand::IMM_IVAL, array_node->get_symbol()->get_offset())));

  // 生成索引值
  Operand index_val = index_node->get_operand(); // 索引值
  Operand expand_index(Operand::VREG, get_next_vreg()); // 临时寄存器用于扩展索引
  Operand extended_index(Operand::VREG, get_next_vreg()); // 临时寄存器用于扩展索引
  get_hl_iseq()->append(new Instruction(HINS_mov_l, expand_index, index_val));

  // 扩展索引值（使用 sconv_lq）
  get_hl_iseq()->append(new Instruction(
      HINS_sconv_lq, extended_index, expand_index));

  // 计算索引偏移（索引值 * 元素大小）
  Operand offset(Operand::VREG, get_next_vreg()); // 临时寄存器用于偏移
  get_hl_iseq()->append(new Instruction(
      HINS_mul_q, offset, extended_index, Operand(Operand::IMM_IVAL, elem_size)));

  // 计算元素地址（基地址 + 偏移量）
  Operand element_addr(Operand::VREG, get_next_vreg()); // 临时寄存器用于元素地址
  get_hl_iseq()->append(new Instruction(
      HINS_add_q, element_addr, base_offset, offset));

  // 将元素地址作为结果存储到节点中
  Operand element_addr_reg(Operand::VREG_MEM, m_next_vreg - 1);
  n->set_operand(element_addr_reg);
}

void HighLevelCodegen::visit_variable_ref(Node *n) {
  // 获取变量的符号信息
  Symbol *symbol = n->get_symbol();
  if (!symbol) {
    RuntimeError::raise("Symbol information missing for variable reference.");
  }

  Operand operand;
  std::shared_ptr<Type> type = symbol->get_type();

  // 检查变量是否分配了虚拟寄存器
  if (symbol->is_in_reg()) {
    // 如果变量在虚拟寄存器中，则直接使用该寄存器
    operand = Operand(Operand::VREG, symbol->get_vreg());
  } else {
    // 如果变量在栈上，根据类型选择适当的内存操作数类型
    int offset = symbol->get_offset();

    // 根据基本类型选择内存操作数
    if (type->is_basic()) {
      switch (type->get_basic_type_kind()) {
        case BasicTypeKind::CHAR:
          operand = Operand(Operand::MREG8, offset);
        break;
        case BasicTypeKind::SHORT:
          operand = Operand(Operand::MREG16, offset);
        break;
        case BasicTypeKind::INT:
          operand = Operand(Operand::MREG32, offset);
        break;
        case BasicTypeKind::LONG:
          operand = Operand(Operand::MREG64, offset);
        break;
        default:
          RuntimeError::raise("Unsupported basic type for variable reference.");
      }
    } else  {
      operand = Operand(Operand::VREG_MEM, offset);
    }
  }

  // 将操作数存储在节点中
  n->set_operand(operand);
}

void HighLevelCodegen::visit_literal_value(Node *n) {
  std::shared_ptr<LiteralValue> val = n->get_literal();
  std::shared_ptr<Type> type = n->get_type();
  int vreg = get_next_vreg();
  Operand dest(Operand::VREG, vreg);

  if (type->is_basic()) {
    HighLevelOpcode mov_opcode = get_opcode(HINS_mov_b, type);

    if (type->get_basic_type_kind() == BasicTypeKind::CHAR) {
      get_hl_iseq()->append(new Instruction(mov_opcode, dest, Operand(Operand::IMM_IVAL, val->get_char_value())));
    } else {
      get_hl_iseq()->append(new Instruction(mov_opcode, dest, Operand(Operand::IMM_IVAL, val->get_int_value())));
    }
  } else if (type->is_pointer() && type->get_base_type()->is_const()) {
    // 字符串常量的字面值
    Operand string_operand(Operand::LABEL, "str" + next_label());
    get_hl_iseq()->append(new Instruction(HINS_mov_q, dest, string_operand)); // 指针常量类型使用 mov_q
  } else {
    RuntimeError::raise("Unsupported literal type in code generation.");
  }

  n->set_operand(dest);
}

void HighLevelCodegen::visit_implicit_conversion(Node *n) {
  // TODO: implement
}

std::string HighLevelCodegen::next_label() {
  std::string label = ".L" + std::to_string(m_next_label_num++);
  return label;
}

int HighLevelCodegen::get_next_vreg() {
  ++m_next_vreg;
  return m_next_vreg - 1;
}

HighLevelOpcode HighLevelCodegen::get_typed_opcode(HighLevelOpcode base_opcode, std::shared_ptr<Type> type) {
  if (type->is_basic()) {
    switch (type->get_basic_type_kind()) {
      case BasicTypeKind::CHAR: return static_cast<HighLevelOpcode>(int(base_opcode) + 0); // `_b`
      case BasicTypeKind::SHORT: return static_cast<HighLevelOpcode>(int(base_opcode) + 1); // `_w`
      case BasicTypeKind::INT: return static_cast<HighLevelOpcode>(int(base_opcode) + 2); // `_l`
      case BasicTypeKind::LONG: return static_cast<HighLevelOpcode>(int(base_opcode) + 3); // `_q`
      default:
        RuntimeError::raise("Unsupported type kind for opcode generation");
    }
  } else if (type->is_pointer()) {
    // 通常指针类型使用 `_l` 表示 LONG 类型
    return static_cast<HighLevelOpcode>(int(base_opcode) + 2); // `_l`
  } else {
    RuntimeError::raise("Attempt to use unsupported type in opcode selection");
  }
}


// TODO: additional private member functions
