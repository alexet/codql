// generated by codegen/codegen.py
import codeql.swift.elements.expr.ApplyExpr

class CallExprBase extends @call_expr, ApplyExpr {
  override string getAPrimaryQlClass() { result = "CallExpr" }
}
