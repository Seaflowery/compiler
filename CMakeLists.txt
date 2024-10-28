cmake_minimum_required(VERSION 3.16)
project(nearly_cc LANGUAGES CXX)

# 设置 C++ 标准和编译选项
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED YES)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -g -Wall")

# 设置源文件路径
set(PARSER_SRC ${CMAKE_SOURCE_DIR}/parse_buildast.y)
set(LEXER_SRC ${CMAKE_SOURCE_DIR}/lex.l)

# 生成解析器文件（Bison）
add_custom_command(
        OUTPUT ${CMAKE_BINARY_DIR}/build/parse.tab.cpp ${CMAKE_BINARY_DIR}/build/parse.tab.h
        COMMAND bison -v --output-file=${CMAKE_BINARY_DIR}/build/parse.tab.cpp --defines=${CMAKE_BINARY_DIR}/build/parse.tab.h ${PARSER_SRC}
        DEPENDS ${PARSER_SRC}
        COMMENT "Generating parser with Bison"
)

# 生成词法分析器文件（Flex）
add_custom_command(
        OUTPUT ${CMAKE_BINARY_DIR}/build/lex.yy.cpp ${CMAKE_BINARY_DIR}/build/lex.yy.h
        COMMAND flex --outfile=${CMAKE_BINARY_DIR}/build/lex.yy.cpp --header-file=${CMAKE_BINARY_DIR}/build/lex.yy.h ${LEXER_SRC}
        DEPENDS ${LEXER_SRC}
        COMMENT "Generating lexer with Flex"
)

# 生成 grammar_symbols 文件
add_custom_command(
        OUTPUT ${CMAKE_BINARY_DIR}/build/grammar_symbols.cpp ${CMAKE_BINARY_DIR}/build/grammar_symbols.h
        COMMAND ruby ${CMAKE_SOURCE_DIR}/scripts/scan_grammar_symbols.rb < ${PARSER_SRC}
        DEPENDS ${PARSER_SRC} ${CMAKE_SOURCE_DIR}/scripts/scan_grammar_symbols.rb
        COMMENT "Generating grammar symbols"
)

add_custom_target(generate_grammar_symbols
        DEPENDS ${CMAKE_BINARY_DIR}/build/grammar_symbols.cpp ${CMAKE_BINARY_DIR}/build/grammar_symbols.h
)

# 生成 ast.cpp 和 ast_visitor 文件
add_custom_command(
        OUTPUT ${CMAKE_BINARY_DIR}/build/ast.cpp ${CMAKE_BINARY_DIR}/build/ast_visitor.h ${CMAKE_BINARY_DIR}/build/ast_visitor.cpp
        COMMAND ruby ${CMAKE_SOURCE_DIR}/scripts/gen_ast_code.rb < ${CMAKE_SOURCE_DIR}/include/ast.h
        DEPENDS ${CMAKE_SOURCE_DIR}/include/ast.h ${CMAKE_SOURCE_DIR}/scripts/gen_ast_code.rb
        COMMENT "Generating AST files"
)

add_custom_target(generate_ast_files
        DEPENDS ${CMAKE_BINARY_DIR}/build/ast.cpp ${CMAKE_BINARY_DIR}/build/ast_visitor.h ${CMAKE_BINARY_DIR}/build/ast_visitor.cpp
)

# 生成 highlevel 文件
add_custom_command(
        OUTPUT ${CMAKE_BINARY_DIR}/build/highlevel.h ${CMAKE_BINARY_DIR}/build/highlevel.cpp
        COMMAND ruby ${CMAKE_SOURCE_DIR}/scripts/gen_highlevel_ir.rb
        DEPENDS ${CMAKE_SOURCE_DIR}/scripts/gen_highlevel_ir.rb
        COMMENT "Generating highlevel IR files"
)

add_custom_target(generate_highlevel_files
        DEPENDS ${CMAKE_BINARY_DIR}/build/highlevel.h ${CMAKE_BINARY_DIR}/build/highlevel.cpp
)

# 将生成的文件添加到源文件列表
set(GENERATED_SRCS
        ${CMAKE_BINARY_DIR}/build/parse.tab.cpp
        ${CMAKE_BINARY_DIR}/build/lex.yy.cpp
        ${CMAKE_BINARY_DIR}/build/grammar_symbols.cpp
        ${CMAKE_BINARY_DIR}/build/ast.cpp
        ${CMAKE_BINARY_DIR}/build/ast_visitor.cpp
        ${CMAKE_BINARY_DIR}/build/highlevel.cpp
)

set(GENERATED_HDRS
        ${CMAKE_BINARY_DIR}/build/parse.tab.h
        ${CMAKE_BINARY_DIR}/build/lex.yy.h
        ${CMAKE_BINARY_DIR}/build/grammar_symbols.h
        ${CMAKE_BINARY_DIR}/build/ast_visitor.h
        ${CMAKE_BINARY_DIR}/build/highlevel.h
)

# 手动指定其他源文件
file(GLOB AST_SRCS ast/*.cpp)
file(GLOB DRIVER_SRCS driver/*.cpp)
file(GLOB HL_CODEGEN_SRCS hl_codegen/*.cpp)
file(GLOB LINEAR_IR_SRCS linear_ir/*.cpp)
file(GLOB LL_CODEGEN_SRCS ll_codegen/*.cpp)
file(GLOB SEMA_SRCS sema/*.cpp)

# 所有源文件
set(SRCS
        ${AST_SRCS}
        ${DRIVER_SRCS}
        ${HL_CODEGEN_SRCS}
        ${LINEAR_IR_SRCS}
        ${LL_CODEGEN_SRCS}
        ${SEMA_SRCS}
        ${GENERATED_SRCS}
)

# 添加可执行文件
add_executable(nearly_cc ${SRCS})

# 添加生成文件的依赖关系
add_dependencies(nearly_cc generate_grammar_symbols generate_ast_files generate_highlevel_files)

# 设置包含目录
target_include_directories(nearly_cc PRIVATE ${CMAKE_SOURCE_DIR}/include ${CMAKE_BINARY_DIR}/build)
