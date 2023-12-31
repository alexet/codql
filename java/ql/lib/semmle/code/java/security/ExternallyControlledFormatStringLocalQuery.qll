/** Provides a taint-tracking configuration to reason about externally-controlled format strings from local sources. */

import java
private import semmle.code.java.dataflow.FlowSources
private import semmle.code.java.StringFormat

/** A taint-tracking configuration to reason about externally-controlled format strings from local sources. */
module ExternallyControlledFormatStringLocalConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof LocalUserInput }

  predicate isSink(DataFlow::Node sink) {
    sink.asExpr() = any(StringFormat formatCall).getFormatArgument()
  }
}

/**
 * Taint-tracking flow for externally-controlled format strings from local sources.
 */
module ExternallyControlledFormatStringLocalFlow =
  TaintTracking::Global<ExternallyControlledFormatStringLocalConfig>;
