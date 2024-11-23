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
#include "symtab.h"
#include "local_storage_allocation.h"

#include <ast.h>

LocalStorageAllocation::LocalStorageAllocation()
  : m_total_local_storage(0U)
  , m_next_vreg(VREG_FIRST_LOCAL)
  , m_next_arg(VREG_FIRST_ARG) {
}

LocalStorageAllocation::~LocalStorageAllocation() {
}

void LocalStorageAllocation::allocate_storage(std::shared_ptr<Function> function) {
  // Any member function can use m_function to refer to the
  // Function object.
  m_function = function;
  m_storage_calc = StorageCalculator(StorageCalculator::STRUCT, 0);

  visit(function->get_funcdef_ast());
  m_storage_calc.finish();
  m_total_local_storage = m_storage_calc.get_size();
  function->get_symbol()->set_offset(m_total_local_storage);
  if (m_return_offset != -1)
    function->get_symbol()->set_return_offset(m_return_offset);
  function->set_next_reg(m_next_vreg);
}

void LocalStorageAllocation::visit_statement_list(Node *n) {
  for (auto it = n->cbegin(); it != n->cend(); ++it) {
    visit(*it);
    if ((*it)->get_tag() == AST_RETURN_STATEMENT) {
      std::shared_ptr<Type> type = (*it)->get_type();
      if (!(type->is_basic() || type->is_pointer())) {
        m_return_offset = m_storage_calc.add_field(type);
      }
    }
  }
}


void LocalStorageAllocation::visit_function_parameter_list(Node *n) {
  for (auto it = n->cbegin(); it != n->cend(); ++it) {
    Node *param = *it;
    allocate_storage_by_type(param->get_symbol());
  }
}

void LocalStorageAllocation::visit_variable_declaration(Node *n) {
  Node *declarator_list_node = n->get_kid(2);
  for (size_t i = 0; i < declarator_list_node->get_num_kids(); ++i) {
    Node *declarator_node = declarator_list_node->get_kid(i);
    Symbol *declarator_symbol = declarator_node->get_symbol();
    allocate_storage_by_type(declarator_symbol);
  }
}


void LocalStorageAllocation::allocate_storage_by_type(Symbol *symbol) {
  if ((symbol->get_type()->is_basic() || symbol->get_type()->is_pointer())
    && !symbol->is_address_taken()) {
      symbol->set_vreg(m_next_vreg++);
   } else {
     unsigned offset = m_storage_calc.add_field(symbol->get_type());
     symbol->set_offset(offset);
   }
}

