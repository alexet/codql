/**
 * Provides modeling for `net-ldap` a ruby library for LDAP.
 */

private import ruby
private import codeql.ruby.ApiGraphs
private import codeql.ruby.dataflow.FlowSummary
private import codeql.ruby.Concepts

/**
 * Provides modeling for `net-ldap` a ruby library for LDAP.
 */
module NetLdap {
  /**
   * Flow summary for `Net::LDAP.new`. This method establishes a connection to a LDAP server.
   */
  private class LdapConnSummary extends SummarizedCallable {
    LdapConnSummary() { this = "Net::LDAP.new" }

    override MethodCall getACall() { result = any(NetLdapConnection l).asExpr().getExpr() }

    override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
      input = "Argument[0]" and output = "ReturnValue" and preservesValue = false
    }
  }

  /**
   * Flow summary for `Net::LDAP.Filter`.
   */
  private class LdapFilterSummary extends SummarizedCallable {
    LdapFilterSummary() { this = "Net::LDAP::Filter" }

    override MethodCall getACall() { result = any(NetLdapFilter l).asExpr().getExpr() }

    override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
      input = ["Argument[0]", "Argument[1]"] and output = "ReturnValue" and preservesValue = false
    }
  }

  /** Net LDAP Api Node */
  private API::Node ldap() { result = API::getTopLevelMember("Net").getMember("LDAP") }

  /** A call that establishes a LDAP Connection */
  private class NetLdapConnection extends DataFlow::CallNode {
    NetLdapConnection() { this in [ldap().getAnInstantiation(), ldap().getAMethodCall("open")] }
  }

  /** A call that constructs a LDAP query */
  private class NetLdapFilter extends LdapConstruction::Range, DataFlow::CallNode {
    NetLdapFilter() {
      this =
        any(ldap()
                .getMember("Filter")
                .getAMethodCall([
                    "begins", "bineq", "contains", "ends", "eq", "equals", "ex", "ge", "le", "ne",
                    "present"
                  ])
        )
    }

    override DataFlow::Node getQuery() { result = this.getArgument([0, 1]) }
  }

  /** A call considered as a LDAP execution. */
  private class NetLdapExecution extends LdapExecution::Range, DataFlow::CallNode {
    NetLdapExecution() { this = any(NetLdapConnection l).getAMethodCall("search") }

    override DataFlow::Node getQuery() { result = this.getKeywordArgument(_) }
  }
}
