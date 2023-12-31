/**
 * Provides models of commonly used functions in the official Couchbase Go SDK library.
 */

import go

/**
 * Provides models of commonly used functions in the official Couchbase Go SDK library.
 */
module Couchbase {
  /**
   * Gets a package path for the official Couchbase Go SDK library.
   *
   * Note that v1 and v2 have different APIs, but the names are disjoint so there is no need to
   * distinguish between them.
   */
  string packagePath() {
    result =
      package([
          "gopkg.in/couchbase/gocb", "github.com/couchbase/gocb", "github.com/couchbaselabs/gocb"
        ], "")
  }

  /**
   * A query used in an API function acting on a `Bucket` or `Cluster` struct of v1 of
   * the official Couchbase Go library, gocb.
   */
  private class CouchbaseV1Query extends NoSql::Query::Range {
    CouchbaseV1Query() {
      // func (b *Bucket) ExecuteAnalyticsQuery(q *AnalyticsQuery, params interface{}) (AnalyticsResults, error)
      // func (b *Bucket) ExecuteN1qlQuery(q *N1qlQuery, params interface{}) (QueryResults, error)
      // func (c *Cluster) ExecuteAnalyticsQuery(q *AnalyticsQuery, params interface{}) (AnalyticsResults, error)
      // func (c *Cluster) ExecuteN1qlQuery(q *N1qlQuery, params interface{}) (QueryResults, error)
      exists(Method meth, string structName, string methodName |
        structName in ["Bucket", "Cluster"] and
        methodName in ["ExecuteN1qlQuery", "ExecuteAnalyticsQuery"] and
        meth.hasQualifiedName(packagePath(), structName, methodName) and
        this = meth.getACall().getArgument(0)
      )
    }
  }

  /**
   * A query used in an API function acting on a `Bucket` or `Cluster` struct of v1 of
   * the official Couchbase Go library, gocb.
   */
  private class CouchbaseV2Query extends NoSql::Query::Range {
    CouchbaseV2Query() {
      // func (c *Cluster) AnalyticsQuery(statement string, opts *AnalyticsOptions) (*AnalyticsResult, error)
      // func (c *Cluster) Query(statement string, opts *QueryOptions) (*QueryResult, error)
      // func (s *Scope) AnalyticsQuery(statement string, opts *AnalyticsOptions) (*AnalyticsResult, error)
      // func (s *Scope) Query(statement string, opts *QueryOptions) (*QueryResult, error)
      exists(Method meth, string structName, string methodName |
        structName in ["Cluster", "Scope"] and
        methodName in ["AnalyticsQuery", "Query"] and
        meth.hasQualifiedName(packagePath(), structName, methodName) and
        this = meth.getACall().getArgument(0)
      )
    }
  }
}
