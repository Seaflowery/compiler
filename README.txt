readme
General Workflow:
* AST Traversal: The semantic analyzer visits each node in the AST, processes its type or declaration, and adds relevant information to the symbol table.
* Symbol Table Population: For each variable, function, or type encountered, an entry is added to the appropriate symbol table, either global or local.
* Type Checking: The analyzer performs semantic checks, such as ensuring correct type assignments and valid operations between different types.
* Error Handling: If semantic errors (like type mismatches or undefined variables) are encountered, the analyzer raises appropriate errors to ensure the program is semantically valid.
