// generated by codegen/codegen.py
import codeql.swift.elements.expr.Expr
import codeql.swift.elements.stmt.Stmt

class ReturnStmtBase extends @return_stmt, Stmt {
  override string getAPrimaryQlClass() { result = "ReturnStmt" }

  Expr getResult() {
    exists(Expr x |
      return_stmt_results(this, x) and
      result = x.resolve()
    )
  }

  predicate hasResult() { exists(getResult()) }
}
