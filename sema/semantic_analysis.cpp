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
#include <algorithm>
#include <utility>
#include <map>
#include "grammar_symbols.h"
#include "parse.tab.h"
#include "node.h"
#include "ast.h"
#include "exceptions.h"
#include "semantic_analysis.h"

#include <unistd.h>

SemanticAnalysis::SemanticAnalysis(const Options &options)
  : m_options(options)
  , m_global_symtab(new SymbolTable(nullptr, "global")) {
  m_cur_symtab = m_global_symtab;
  m_all_symtabs.push_back(m_global_symtab);
}

SemanticAnalysis::~SemanticAnalysis() {
  // The semantic analyzer owns the SymbolTables and their Symbols,
  // so delete them. Note that the AST has pointers to Symbol objects,
  // so the SemanticAnalysis object should live at least as long
  // as the AST.
  for (auto i = m_all_symtabs.begin(); i != m_all_symtabs.end(); ++i)
    delete *i;
}

void SemanticAnalysis::visit_struct_type(Node *n) {
  std::string struct_name = "struct " + n->get_kid(0)->get_str();
  Symbol *symbol = m_cur_symtab->lookup_recursive(struct_name);
  if (symbol == nullptr) {
    SemanticError::raise(n->get_loc(), "undefined struct");
  }
  n->set_symbol(symbol);
}

void SemanticAnalysis::visit_union_type(Node *n) {
  RuntimeError::raise("union types aren't supported");
}

void SemanticAnalysis::visit_declarator_list_node(Node *n) {
  if (n->get_tag() == AST_NAMED_DECLARATOR) {
    visit_named_declarator(n);
  } else if (n->get_tag() == AST_ARRAY_DECLARATOR) {
    visit_array_declarator(n);
  } else if (n->get_tag() == AST_POINTER_DECLARATOR) {
    visit_pointer_declarator(n);
  }
}


void SemanticAnalysis::visit_named_declarator(Node *n) {
  assert(n != nullptr);
  n->set_str(n->get_kid(0)->get_str());
}

void SemanticAnalysis::visit_pointer_declarator(Node *n) {
  Node* kid = n->get_kid(0);
  std::shared_ptr<Type> type = std::make_shared<PointerType>(n->get_type());
  kid->set_type(type);
  visit_declarator_list_node(kid);
  n->set_str(kid->get_str());
  n->set_type(kid->get_type());
}

void SemanticAnalysis::visit_array_declarator(Node *n) {
  Node *kid = n->get_kid(0);
  int size = 0;
  try {
    size = stoi(n->get_kid(1)->get_str());
  } catch (const std::invalid_argument& e) {
    SemanticError::raise(n->get_loc(), "invalid array len");
  }
  std::shared_ptr<Type> type = std::make_shared<ArrayType>(n->get_type(), size);
  if (size == 0)
    type = std::make_shared<PointerType>(n->get_type());
  kid->set_type(type);
  visit_declarator_list_node(kid);
  n->set_str(kid->get_str());
  n->set_type(kid->get_type());
}


void SemanticAnalysis::visit_variable_declaration(Node *n) {
  n->set_symbolTable(m_cur_symtab);
  assert(n != nullptr);

  Node *storage_node = n->get_kid(0);
  SymbolTable *target_symtab = m_cur_symtab;

  if (storage_node->get_tag() == TOK_EXTERN) {
    target_symtab = m_global_symtab;
  }

  Node *basic_type_node = n->get_kid(1);
  visit_basic_type(basic_type_node);
  std::shared_ptr<Type> base_type = basic_type_node->get_type();

  Node *declarator_list_node = n->get_kid(2);
  for (size_t i = 0; i < declarator_list_node->get_num_kids(); ++i) {
    Node *declarator_node = declarator_list_node->get_kid(i);
    declarator_node->set_type(base_type);

    visit_declarator_list_node(declarator_node);
    std::string var_name = declarator_node->get_kid(0)->get_str();
    std::shared_ptr<Type> var_type = declarator_node->get_type();
    if (target_symtab->has_symbol_local(var_name)) {
      SemanticError::raise(n->get_loc(), "variable defined");
    }

    target_symtab->add_entry(declarator_node->get_loc(),
      SymbolKind::VARIABLE, var_name, var_type);
  }
}


void SemanticAnalysis::visit_basic_type(Node *n) {
  assert(n != nullptr);
  if (n->get_tag() == AST_STRUCT_TYPE) {
    visit_struct_type(n);
    return;
  }


  if (n->get_tag() != AST_BASIC_TYPE) {
    SemanticError::raise(n->get_loc(), "Expected basic type node");
    return;
  }

  bool is_const = false;
  bool is_volatile = false;
  bool is_unsigned = false;
  BasicTypeKind type_kind = BasicTypeKind::INT;
  bool is_int = false;

  for (size_t i = 0; i < n->get_num_kids(); ++i) {
    Node *child = n->get_kid(i);
    switch (child->get_tag()) {
      case TOK_CONST:
        if (is_const || is_volatile)
          SemanticError::raise(n->get_loc(), "wrong type");
        is_const = true;
      break;
      case TOK_VOLATILE:
        if (is_const || is_volatile)
          SemanticError::raise(n->get_loc(), "wrong type");
        is_volatile = true;
      break;
      case TOK_UNSIGNED:
        is_unsigned = true;
      break;
      case TOK_SIGNED:
        if (is_unsigned)
          SemanticError::raise(n->get_loc(), "wrong type");
        is_unsigned = false;
      break;
      case TOK_INT:
        is_int = true;
        if (type_kind != BasicTypeKind::LONG && type_kind != BasicTypeKind::SHORT)
          type_kind = BasicTypeKind::INT;
      break;
      case TOK_CHAR:
        if (type_kind != BasicTypeKind::INT || is_int) {
          SemanticError::raise(n->get_loc(), "wrong type");
        }
        type_kind = BasicTypeKind::CHAR;
      break;
      case TOK_SHORT:
        if (type_kind != BasicTypeKind::INT) {
          SemanticError::raise(n->get_loc(), "wrong type");
        }
        type_kind = BasicTypeKind::SHORT;
      break;
      case TOK_LONG:
        if (type_kind != BasicTypeKind::INT) {
          SemanticError::raise(n->get_loc(), "wrong type");
        }
        type_kind = BasicTypeKind::LONG;
      break;
      case TOK_VOID:
        if (is_int || is_const || is_volatile || type_kind != BasicTypeKind::INT) {
          SemanticError::raise(n->get_loc(), "wrong type");
        }
        type_kind = BasicTypeKind::VOID;
      break;
      default:
        SemanticError::raise(n->get_loc(), "Unrecognized token in basic type");
    }
  }

  std::shared_ptr<Type> basic_type = std::make_shared<BasicType>(type_kind, !is_unsigned);

  if (is_const) {
    basic_type = std::make_shared<QualifiedType>(basic_type, TypeQualifier::CONST);
  }
  if (is_volatile) {
    basic_type = std::make_shared<QualifiedType>(basic_type, TypeQualifier::VOLATILE);
  }

  n->set_type(basic_type);
}

void SemanticAnalysis::visit_declarator_list(Node *n) {}


void SemanticAnalysis::visit_function_declaration(Node *n) {
  n->set_symbolTable(m_cur_symtab);
  Node *type_node = n->get_kid(0);
  visit_basic_type(type_node);
  std::shared_ptr<Type> return_type = type_node->get_type();
  std::shared_ptr<Type> func_type = std::make_shared<FunctionType>(return_type);

  std::string func_name = n->get_kid(1)->get_str();
  if ((func_name == "main") && m_cur_symtab != m_global_symtab) {
    SemanticError::raise(n->get_loc(), "main function not in global scope");
  }

  // analyze param type and update function type
  Node *param_list = n->get_kid(2);
  analyze_param_type(param_list, func_type);

  // check if the function is already defined, if yes, rename the params
  bool added = add_func(func_name, func_type, n);

  if (!added) {
    SymbolTable *fn_symtab = enter_scope("function " + func_name);
    // check and add param to symbol table
    visit_param_list(param_list, func_type);
    leave_scope();
  }

}

void SemanticAnalysis::visit_function_definition(Node *n) {
  Node *type_node = n->get_kid(0);
  visit_basic_type(type_node);
  std::shared_ptr<Type> return_type = type_node->get_type();
  std::shared_ptr<Type> func_type = std::make_shared<FunctionType>(return_type);

  std::string func_name = n->get_kid(1)->get_str();
  if ((func_name == "main") && m_cur_symtab != m_global_symtab) {
    SemanticError::raise(n->get_loc(), "main function not in global scope");
  }

  // analyze param type and update function type
  Node *param_list = n->get_kid(2);
  analyze_param_type(param_list, func_type);

  // check if the function is already defined, if yes, rename the params
  bool added = add_func(func_name, func_type, n);

  if (!added) {
    SymbolTable *fn_symtab = enter_scope("function " + func_name);
    fn_symtab->set_fn_type(func_type);
    // check and add param to symbol table
    visit_param_list(param_list, func_type);
    // analyze function body
    visit_statement_list(n->get_kid(3));
    leave_scope();
  }
}

bool SemanticAnalysis::add_func(std::string &func_name, std::shared_ptr<Type> &func_type, Node *n) {
  Symbol *symbol = m_cur_symtab->lookup_recursive(func_name);
  if (symbol != nullptr) {
    if (symbol->get_kind() != SymbolKind::FUNCTION || !func_type->is_same(symbol->get_type().get())) {
      SemanticError::raise(n->get_loc(), "function name defined");
    } else {
      std::shared_ptr<Type> stored = symbol->get_type();
      for (int i = 0; i < stored->get_num_members(); ++i) {
        Member member = stored->get_member(i);
        std::shared_ptr<FunctionType> t = std::dynamic_pointer_cast<FunctionType>(func_type);
        member.set_name(t->get_modify_member(i).get_name());
      }
    }
    return true;
  } else {
    m_cur_symtab->add_entry(n->get_loc(), SymbolKind::FUNCTION, func_name, func_type);
  }
  return false;
}

void SemanticAnalysis::visit_statement_list(Node *n) {
  for (size_t i = 0; i < n->get_num_kids(); ++i) {
    Node *stmt = n->get_kid(i);
    switch (stmt->get_tag()) {
      case AST_VARIABLE_DECLARATION:
          visit_variable_declaration(stmt);
      break;
      case AST_EXPRESSION_STATEMENT:
          visit_expression_statement(stmt);
      break;
      case AST_RETURN_EXPRESSION_STATEMENT:
          visit_return_expression_statement(stmt);
      break;
      case AST_FOR_STATEMENT:
      case AST_WHILE_STATEMENT:
      case AST_IF_STATEMENT:
        visit_conditional_expression(stmt);
      break;
      case AST_IF_ELSE_STATEMENT:
        visit_if_else_statement(stmt);
      break;
      default:
        SemanticError::raise(stmt->get_loc(), "Unknown statement type.");
    }
  }
}

void SemanticAnalysis::visit_expression_statement(Node *n) {
  Node *expr = n->get_kid(0);
  visit_expression(expr);
}

void SemanticAnalysis::analyze_param_type(Node *n, std::shared_ptr<Type> &func_type) {
  for (auto it = n->cbegin(); it != n->cend(); ++it) {
    Node *node = *it;
    visit_function_parameter(node);
    const std::shared_ptr<Type> paramType = node->get_type();
    std::string param_name = node->get_str();
    func_type->add_member(*new Member(param_name, paramType));
  }
}


void SemanticAnalysis::visit_param_list(Node *n, std::shared_ptr<Type> &func_type) {
  n->set_symbolTable(m_cur_symtab);
  for (int i = 0; i < func_type->get_num_members(); ++i) {
    Member member = func_type->get_member(i);
    const std::string& param_name = member.get_name();
    std::shared_ptr<Type> param_type = member.get_type();
    if (m_cur_symtab->has_symbol_local(param_name)) {
      SemanticError::raise(n->get_loc(), "parameter name conflicts");
    }
    const Node *node = n->get_kid(i);
    m_cur_symtab->add_entry(node->get_loc(), SymbolKind::VARIABLE, param_name, param_type);
  }
}

void SemanticAnalysis::visit_function_parameter(Node *n) {
  Node *type_node = n->get_kid(0);
  visit_basic_type(type_node);
  std::shared_ptr<Type> base_type = type_node->get_type();
  Node *top_node = n->get_kid(1);
  top_node->set_type(base_type);
  visit_declarator_list_node(top_node);
  n->set_type(top_node->get_type());
  n->set_str(top_node->get_str());
}

void SemanticAnalysis::visit_function_parameter_list(Node *n) {}

void SemanticAnalysis::visit_expression(Node *n) {
    assert(n != nullptr);
    switch (n->get_tag()) {
      case AST_BINARY_EXPRESSION:
        visit_binary_expression(n);
      break;
      case AST_UNARY_EXPRESSION:
        visit_unary_expression(n);
      break;
      case AST_POSTFIX_EXPRESSION:
        visit_postfix_expression(n);
      break;
      case AST_CONDITIONAL_EXPRESSION:
        visit_conditional_expression(n);
      break;
      case AST_CAST_EXPRESSION:
        visit_cast_expression(n);
      break;
      case AST_VARIABLE_REF:
        visit_variable_ref(n);
      break;
      case AST_LITERAL_VALUE:
        visit_literal_value(n);
      break;
      case AST_ARRAY_ELEMENT_REF_EXPRESSION:
        visit_array_element_ref_expression(n);
      break;
      case AST_FUNCTION_CALL_EXPRESSION:
        visit_function_call_expression(n);
      break;
      case AST_INDIRECT_FIELD_REF_EXPRESSION:
        visit_indirect_field_ref_expression(n);
      break;
      case AST_FIELD_REF_EXPRESSION:
        visit_field_ref_expression(n);
      break;
      default:
        SemanticError::raise(n->get_loc(), "Unsupported expression type.");
    }

}


void SemanticAnalysis::visit_return_expression_statement(Node *n) {
  Node *return_expr = n->get_kid(0);
  visit_expression(return_expr);

  std::shared_ptr<Type> expr_type = return_expr->get_type();
  std::shared_ptr<Type> return_type = m_cur_symtab->get_fn_type()->get_base_type();

  if (!expr_type->is_same(return_type.get())) {
    SemanticError::raise(n->get_loc(), "Return type does not match function return type.");
  }
}


void SemanticAnalysis::visit_struct_type_definition(Node *n) {
  std::string struct_name = "struct " + n->get_kid(0)->get_str();
  std::shared_ptr<Type> struct_type = std::make_shared<StructType>(n->get_kid(0)->get_str());
  Node *field_list = n->get_kid(1);

  Symbol *symbol = m_cur_symtab->lookup_recursive(struct_name);
  if (symbol != nullptr && symbol->get_type()->is_struct() && symbol->get_type()->get_num_members() == field_list->get_num_kids()) {
    SemanticError::raise(n->get_loc(), "struct name conflict");
  }
  m_cur_symtab->add_entry(n->get_loc(), SymbolKind::TYPE, struct_name, struct_type);

  enter_scope(struct_name);
    for (auto it = field_list->cbegin(); it != field_list->cend(); ++it) {
      visit_variable_declaration(*it);
      Node *var_node =(*it)->get_kid(2);
      for (auto it = var_node->cbegin(); it != var_node->cend(); ++it) {
        std::string var_name = (*it)->get_str();
        struct_type->add_member(*new Member(var_name, (*it)->get_type()));
      }

    }
  leave_scope();
}

bool SemanticAnalysis::is_lvalue(Node *n) {
  int tag = n->get_tag();
  if (tag == AST_VARIABLE_REF || tag == AST_ARRAY_ELEMENT_REF_EXPRESSION ||
    tag == AST_UNARY_EXPRESSION && n->get_kid(0)->get_tag() == TOK_ASTERISK ||
    tag == AST_FIELD_REF_EXPRESSION || tag == AST_INDIRECT_FIELD_REF_EXPRESSION) {
    return true;
    }
  return false;
}

void SemanticAnalysis::visit_assignment_expression(Node *lhs, std::shared_ptr<Type> rhs_type) {
  if (!is_lvalue(lhs)) {
    SemanticError::raise(lhs->get_loc(), "Left-hand side of assignment must be an lvalue.");
  }
  check_assignment_type(lhs->get_loc(), lhs->get_type(), rhs_type);
}

void SemanticAnalysis::check_assignment_type(const Location& loc, std::shared_ptr<Type> lhs_type, std::shared_ptr<Type> rhs_type) {

  if ((lhs_type->is_pointer() || lhs_type->is_array()) && (rhs_type->is_pointer() || rhs_type->is_array())) {
    check_pointer_assignment(loc, lhs_type, rhs_type);
  } else if (lhs_type->is_struct() && rhs_type->is_struct()) {
    if (!lhs_type->is_same(rhs_type.get())) {
      SemanticError::raise(loc, "Struct type mismatch in assignment.");
    }
  } else if (!(lhs_type->is_integral() && rhs_type->is_integral())) {
    SemanticError::raise(loc, "Type mismatch in assignment.");
  }
}


std::shared_ptr<Type> SemanticAnalysis::get_basic_type(std::shared_ptr<Type> type) {
  while (type->is_pointer() || type->is_array()) {
    type = type->get_base_type();
  }
  return type;
}

std::shared_ptr<Type> SemanticAnalysis::get_naked_type(std::shared_ptr<Type> type) {
  while (type->has_base_type()) {
    type = type->get_base_type();
  }
  return type;
}


void SemanticAnalysis::check_pointer_assignment(const Location& loc, std::shared_ptr<Type> lhs_type, std::shared_ptr<Type> rhs_type) {
  std::shared_ptr<Type> lhs_base_type = get_basic_type(lhs_type);
  std::shared_ptr<Type> rhs_base_type = get_basic_type(rhs_type);

  if (!lhs_base_type->is_const() && rhs_base_type->is_const()) {
    SemanticError::raise(loc, "Cannot assign a non-const pointer to a const-qualified pointer.");
  }

  if (!lhs_base_type->is_volatile() && rhs_base_type->is_volatile()) {
    SemanticError::raise(loc, "Cannot assign a non-volatile pointer to a volatile-qualified pointer.");
  }

  if (!get_naked_type(lhs_base_type)->is_same(get_naked_type(rhs_base_type).get())) {
    SemanticError::raise(loc, "Pointer base type mismatch in assignment.");
  }
}



void SemanticAnalysis::visit_binary_expression(Node *n) {
  assert(n != nullptr);

  Node *operator_node = n->get_kid(0);  // 操作符
  Node *lhs = n->get_kid(1);  // 左操作数
  Node *rhs = n->get_kid(2);  // 右操作数

  visit_expression(lhs);  // 递归解析左操作数
  visit_expression(rhs);  // 递归解析右操作数

  std::shared_ptr<Type> lhs_type = lhs->get_type();
  std::shared_ptr<Type> rhs_type = rhs->get_type();

  // 检查左右操作数是否匹配


  switch (operator_node->get_tag()) {
    case TOK_PLUS:
    case TOK_MINUS:
    case TOK_ASTERISK:
    case TOK_DIVIDE:
    case TOK_MOD:
      visit_arithmetic(n, lhs_type, rhs_type);
    break;

    case TOK_EQUALITY:
    case TOK_INEQUALITY:
    case TOK_LT:
    case TOK_GT:
    case TOK_LTE:
    case TOK_GTE:
        // 比较运算符应该返回布尔类型
        if (!lhs_type->is_integral() || !rhs_type->is_integral()) {
          SemanticError::raise(n->get_loc(), "Comparison operations require integral types.");
        }
    n->set_type(std::make_shared<BasicType>(BasicTypeKind::INT, true));  // 返回 int 表示布尔值
    break;

    case TOK_LOGICAL_AND:
    case TOK_LOGICAL_OR:
      if (!lhs_type->is_integral() || !rhs_type->is_integral()) {
        SemanticError::raise(n->get_loc(), "Logical operations require integral types.");
      }
      n->set_type(std::make_shared<BasicType>(BasicTypeKind::INT, true));  // 返回 int 表示布尔值
      break;

    case TOK_ASSIGN:
      visit_assignment_expression(lhs, rhs->get_type());
    break;

    default:
      SemanticError::raise(n->get_loc(), "Unsupported binary operation.");
  }
}

void SemanticAnalysis::visit_arithmetic(Node *n, std::shared_ptr<Type> lhs_type, std::shared_ptr<Type> rhs_type) {
  if (lhs_type->is_integral() && rhs_type->is_integral()) {
    n->set_type(std::make_shared<BasicType>(BasicTypeKind::INT, true));
  } else if ((lhs_type->is_integral() && rhs_type->is_pointer()) ||
    (lhs_type->is_pointer() && rhs_type->is_integral())) {
    n->set_type(std::make_shared<PointerType>(lhs_type->is_integral() ? lhs_type : rhs_type));
  } else {
    SemanticError::raise(n->get_loc(), "Arithmetic operations require integral types.");
  }
}


void SemanticAnalysis::visit_unary_expression(Node *n) {
  assert(n != nullptr);

  Node *operator_node = n->get_kid(0);  // 操作符
  Node *operand = n->get_kid(1);  // 操作数
  visit_expression(operand);  // 递归解析操作数

  std::shared_ptr<Type> operand_type = operand->get_type();

  switch (operator_node->get_tag()) {
    case TOK_ASTERISK:  // 指针解引用 * 运算符
      if (!operand_type->is_pointer()) {
        SemanticError::raise(n->get_loc(), "Dereference requires a pointer type.");
      }
    n->set_type(operand_type->get_base_type());  // 返回指针指向的类型
    break;

    case TOK_AMPERSAND:
      if (!is_lvalue(operand)) {
        SemanticError::raise(n->get_loc(), "require lvalue to get address");
      }
      n->set_type(std::make_shared<PointerType>(operand_type));  // 返回指向操作数的指针类型
    break;

    case TOK_MINUS:  // 取反 - 运算符
      if (!operand_type->is_integral()) {
        SemanticError::raise(n->get_loc(), "Unary minus requires an integral operand.");
      }
    n->set_type(operand_type);  // 返回操作数的类型
    break;

    case TOK_NOT:  // 逻辑非 ! 运算符
      if (!operand_type->is_integral()) {
        SemanticError::raise(n->get_loc(), "Logical not requires an integral operand.");
      }
    n->set_type(std::make_shared<BasicType>(BasicTypeKind::INT, true));  // 返回 int 类型表示布尔值
    break;

    default:
      SemanticError::raise(n->get_loc(), "Unsupported unary operation.");
  }
}

void SemanticAnalysis::visit_postfix_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_conditional_expression(Node *n) {
  int line = 0;
  for (auto it = n->cbegin(); it != n->cend(); ++it) {
    if ((*it)->get_tag() == AST_STATEMENT_LIST) {
      line = (*it)->get_loc().get_line();
    }
  }
  SymbolTable *symbol_table = enter_scope("block " + std::to_string(line));
  if (n->get_tag() == AST_FOR_STATEMENT) {
    visit_for_statement(n);
  } else if (n->get_tag() == AST_WHILE_STATEMENT) {
    visit_while_statement(n);
  } else if (n->get_tag() == AST_IF_STATEMENT) {
    visit_if_statement(n);
  }
  leave_scope();
}

void SemanticAnalysis::visit_if_else_statement(Node *n) {
  visit(n->get_kid(0));

  Node *if_stmt = n->get_kid(1);
  enter_scope("block " + std::to_string(if_stmt->get_loc().get_line()));
  visit(if_stmt);
  leave_scope();

  Node *else_stmt = n->get_kid(2);
  enter_scope("block " + std::to_string(else_stmt->get_loc().get_line()));
  visit(else_stmt);
  leave_scope();
}


void SemanticAnalysis::visit_cast_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_function_call_expression(Node *n) {
  std::string func_name = n->get_kid(0)->get_kid(0)->get_str();
  Symbol *symbol = m_cur_symtab->lookup_recursive(func_name);
  if (symbol == nullptr) {
    SemanticError::raise(n->get_loc(), "Function name not found.");
  }
  std::shared_ptr<Type> function_type = symbol->get_type();
  Node *arguments = n->get_kid(1);
  if (arguments->get_num_kids() != function_type->get_num_members()) {
    SemanticError::raise(n->get_loc(), "wrong argument number");
  }
  for (int i = 0; i < function_type->get_num_members(); i++) {
    Node *cur_arg = arguments->get_kid(i);
    visit_expression(cur_arg);
    const Member member = function_type->get_member(i);
    check_assignment_type(n->get_loc(), member.get_type(), cur_arg->get_type());
  }

  n->set_type(function_type->get_base_type());
}

void SemanticAnalysis::visit_field_ref_expression(Node *n) {
  Node *var = n->get_kid(0);
  visit_expression(var);
  std::shared_ptr<Type> type = var->get_type();
  if (!type->is_struct()) {
    SemanticError::raise(n->get_loc(), "struct not found");
  }
  // if (var->get_tag() == AST_FIELD_REF_EXPRESSION || var->get_tag() == AST_INDIRECT_FIELD_REF_EXPRESSION)
  //   visit_expression(var);
  std::string field_name = n->get_kid(1)->get_str();
  const std::shared_ptr<Type>& struct_type = type;
  bool found = false;
  for (int i = 0; i < struct_type->get_num_members(); i++) {
    Member member = struct_type->get_member(i);
    if (member.get_name() == field_name) {
      found = true;
      n->set_type(member.get_type());
      break;
    }
  }

  if (!found) {
    SemanticError::raise(n->get_loc(), "struct member not found");
  }
}

void SemanticAnalysis::visit_indirect_field_ref_expression(Node *n) {
  Node *var = n->get_kid(0);
  visit_expression(var);
  std::shared_ptr<Type> type = var->get_type();
  if (!type->is_pointer() || !type->get_base_type()->is_struct()) {
    SemanticError::raise(n->get_loc(), "struct pointer not found");
  }

  std::string field_name = n->get_kid(1)->get_str();
  std::shared_ptr<Type> struct_type = type->get_base_type();
  std::shared_ptr<Type> field_type = type->get_base_type();
  bool found = false;
  for (int i = 0; i < struct_type->get_num_members(); i++) {
    Member member = struct_type->get_member(i);
    if (member.get_name() == field_name) {
      found = true;
      n->set_type(member.get_type());
      break;
    }
  }

  if (!found) {
    SemanticError::raise(n->get_loc(), "struct member not found");
  }
}

void SemanticAnalysis::visit_array_element_ref_expression(Node *n) {
  Node *ref = n->get_kid(0);
  if (ref->get_tag() != AST_VARIABLE_REF) {
    visit_expression(ref);
  } else {
    visit_variable_ref(ref);
  }

  if (!ref->get_type()->is_array() && !ref->get_type()->is_pointer() ) {
    SemanticError::raise(n->get_loc(), "Array reference must be an array or a pointer.");
  }
  // int array_size = ref->get_type()->get_array_size();
  // int access = stoi(n->get_kid(1)->get_str());
  // if (access < 0 || access >= array_size) {
  //   SemanticError::raise(n->get_loc(), "Array out of bounds");
  // }
  if (ref->get_type()->is_pointer() && ref->get_type()->get_base_type()->is_array()) {
    n->set_type(std::make_shared<PointerType>(ref->get_type()->get_base_type()->get_base_type()));
  } else {
    n->set_type(ref->get_type()->get_base_type());
  }
}

void SemanticAnalysis::visit_variable_ref(Node *n) {
  std::string var_name = n->get_kid(0)->get_str();
  Symbol *symbol = m_cur_symtab->lookup_recursive(var_name);
  if (!symbol) {
    SemanticError::raise(n->get_loc(), ("Undeclared variable '" + var_name + "'").c_str());
  }
  n->set_symbol(symbol);
}

void SemanticAnalysis::visit_literal_value(Node *n) {
  std::shared_ptr<Type> type = std::make_shared<BasicType>(BasicTypeKind::INT, true);
  int tag = n->get_kid(0)->get_tag();

  if (tag == TOK_INT_LIT) {
    std::shared_ptr<LiteralValue> value = std::make_shared<LiteralValue>(
      LiteralValue::from_int_literal(n->get_kid(0)->get_str(), n->get_loc()));
    if (value->is_long()) {
      type = std::make_shared<BasicType>(BasicTypeKind::LONG, true);
    } else if (value->is_unsigned()) {
      type = std::make_shared<BasicType>(BasicTypeKind::INT, false);
    }
  } else if (tag == TOK_STR_LIT) {
    auto base_type = std::make_shared<BasicType>(BasicTypeKind::CHAR, true);
    auto qualified = std::make_shared<QualifiedType>(base_type, TypeQualifier::CONST);
    type = std::make_shared<PointerType>(qualified);
  } else if (tag == TOK_CHAR_LIT) {
    type = std::make_shared<BasicType>(BasicTypeKind::CHAR, true);
  } else {
    SemanticError::raise(n->get_loc(), "Unsupported literal type.");
  }

  n->set_type(type);
}


SymbolTable *SemanticAnalysis::enter_scope(const std::string &name) {
  SymbolTable *symtab = new SymbolTable(m_cur_symtab, name);
  m_all_symtabs.push_back(symtab);
  m_cur_symtab = symtab;
  return symtab;
}

void SemanticAnalysis::leave_scope() {
  assert(m_cur_symtab->get_parent() != nullptr);
  m_cur_symtab = m_cur_symtab->get_parent();
}

// TODO: implement helper functions
