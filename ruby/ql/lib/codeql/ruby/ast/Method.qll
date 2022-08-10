private import codeql.ruby.AST
private import codeql.ruby.controlflow.ControlFlowGraph
private import internal.AST
private import internal.TreeSitter
private import internal.Method

/** A callable. */
class Callable extends StmtSequence, Expr, Scope, TCallable {
  /** Gets the number of parameters of this callable. */
  final int getNumberOfParameters() { result = count(this.getAParameter()) }

  /** Gets a parameter of this callable. */
  final Parameter getAParameter() { result = this.getParameter(_) }

  /** Gets the `n`th parameter of this callable. */
  Parameter getParameter(int n) { none() }

  override AstNode getAChild(string pred) {
    result = super.getAChild(pred)
    or
    pred = "getParameter" and result = this.getParameter(_)
  }
}

/** A method. */
class MethodBase extends Callable, BodyStmt, Scope, TMethodBase {
  /** Gets the name of this method. */
  string getName() { none() }

  /** Holds if the name of this method is `name`. */
  final predicate hasName(string name) { this.getName() = name }

  override AstNode getAChild(string pred) {
    result = Callable.super.getAChild(pred)
    or
    result = BodyStmt.super.getAChild(pred)
  }

  /**
   * Holds if this method is public.
   * Methods are public by default.
   */
  predicate isPublic() { this.getVisibility() = "public" }

  /** Holds if this method is private. */
  predicate isPrivate() { this.getVisibility() = "private" }

  /** Holds if this method is protected. */
  predicate isProtected() { this.getVisibility() = "protected" }

  /**
   * Gets a string describing the visibility of this method.
   * This is either 'public', 'private' or 'protected'.
   */
  string getVisibility() {
    result = this.getVisibilityModifier().getVisibility()
    or
    not exists(this.getVisibilityModifier()) and result = "public"
  }

  /**
   * Gets the visibility modifier that defines the visibility of this method, if
   * one exists.
   */
  VisibilityModifier getVisibilityModifier() { none() }
}

/**
 * A method call which modifies another method in some way.
 * For example, `private :foo` makes the method `foo` private.
 */
private class MethodModifier extends MethodCall {
  /** Gets the name of the method that this call applies to. */
  Expr getMethodArgument() { result = this.getArgument(0) }
}

/** A method call that sets the visibility of other methods. */
private class VisibilityModifier extends MethodModifier {
  private Namespace namespace;
  private int position;

  VisibilityModifier() {
    this.getMethodName() =
      ["public", "private", "protected", "public_class_method", "private_class_method"] and
    namespace.getStmt(position) = this
  }

  /**
   * Holds if this modifier changes the "ambient" visibility - i.e. the default
   * visibility of any subsequent method definitions.
   */
  predicate modifiesAmbientVisibility() {
    this.getMethodName() = ["public", "private", "protected"] and
    this.getNumberOfArguments() = 0
  }

  string getVisibility() {
    this.getMethodName() = ["public", "public_class_method"] and result = "public"
    or
    this.getMethodName() = ["private", "private_class_method"] and
    result = "private"
    or
    this.getMethodName() = "protected" and
    result = "protected"
  }
}

/** A normal method. */
class Method extends MethodBase, TMethod {
  private Ruby::Method g;

  Method() { this = TMethod(g) }

  final override string getAPrimaryQlClass() { result = "Method" }

  final override string getName() {
    result = g.getName().(Ruby::Token).getValue() or
    result = g.getName().(Ruby::Setter).getName().getValue() + "="
  }

  /**
   * Holds if this is a setter method, as in the following example:
   * ```rb
   * class Person
   *   def name=(n)
   *     @name = n
   *   end
   * end
   * ```
   */
  final predicate isSetter() { g.getName() instanceof Ruby::Setter }

  /**
   * Holds if this method is private. All methods with the name prefix
   * `private` are private below:
   *
   * ```rb
   * class C
   *   private def private1
   *   end
   *
   *   def public
   *   end
   *
   *   def private2
   *   end
   *   private :private2
   *
   *   private
   *
   *   def private3
   *   end
   *
   *   def private4
   *   end
   * end
   * ```
   */
  override predicate isPrivate() { super.isPrivate() }

  final override Parameter getParameter(int n) {
    toGenerated(result) = g.getParameters().getChild(n)
  }

  final override string toString() { result = this.getName() }

  override string getVisibility() {
    result = this.getVisibilityModifier().getVisibility()
    or
    this.getEnclosingModule() instanceof Toplevel and
    not exists(this.getVisibilityModifier()) and
    result = "private"
    or
    not this.getEnclosingModule() instanceof Toplevel and
    not exists(this.getVisibilityModifier()) and
    result = "public"
  }

  override VisibilityModifier getVisibilityModifier() {
    result.getEnclosingModule() = this.getEnclosingModule() and
    (
      result.getMethodArgument() = this
      or
      result.getMethodArgument().getConstantValue().getStringlikeValue() = this.getName()
    )
    or
    exists(Namespace n, int methodPos | n.getStmt(methodPos) = this |
      // The relevant visibility modifier is the closest call that occurs before
      // the definition of `m` (typically this means higher up the file).
      result =
        max(int modifierPos, VisibilityModifier modifier |
          modifier.modifiesAmbientVisibility() and
          n.getStmt(modifierPos) = modifier and
          modifierPos < methodPos
        |
          modifier order by modifierPos
        )
    )
  }
}

/** A singleton method. */
class SingletonMethod extends MethodBase, TSingletonMethod {
  private Ruby::SingletonMethod g;

  SingletonMethod() { this = TSingletonMethod(g) }

  final override string getAPrimaryQlClass() { result = "SingletonMethod" }

  /** Gets the object of this singleton method. */
  final Expr getObject() { toGenerated(result) = g.getObject() }

  final override string getName() {
    result = g.getName().(Ruby::Token).getValue()
    or
    result = g.getName().(Ruby::Setter).getName().getValue() + "="
  }

  final override Parameter getParameter(int n) {
    toGenerated(result) = g.getParameters().getChild(n)
  }

  final override string toString() { result = this.getName() }

  final override AstNode getAChild(string pred) {
    result = super.getAChild(pred)
    or
    pred = "getObject" and result = this.getObject()
  }

  /**
   * Holds if this method is private. All methods with the name prefix
   * `private` are private below:
   *
   * ```rb
   * class C
   *   private_class_method def self.private1
   *   end
   *
   *   def self.public
   *   end
   *
   *   def self.private2
   *   end
   *   private_class_method :private2
   *
   *   private # this has no effect on singleton methods
   *
   *   def self.public2
   *   end
   * end
   * ```
   */
  override predicate isPrivate() { super.isPrivate() }

  override VisibilityModifier getVisibilityModifier() {
    result.getEnclosingModule() = this.getEnclosingModule() and
    (
      result.getMethodArgument() = this
      or
      result.getMethodArgument().getConstantValue().getStringlikeValue() = this.getName()
    )
  }
}

/**
 * A lambda (anonymous method). For example:
 * ```rb
 * -> (x) { x + 1 }
 * ```
 */
class Lambda extends Callable, BodyStmt, TLambda {
  private Ruby::Lambda g;

  Lambda() { this = TLambda(g) }

  final override string getAPrimaryQlClass() { result = "Lambda" }

  final override Parameter getParameter(int n) {
    toGenerated(result) = g.getParameters().getChild(n)
  }

  final override string toString() { result = "-> { ... }" }

  final override AstNode getAChild(string pred) {
    result = Callable.super.getAChild(pred)
    or
    result = BodyStmt.super.getAChild(pred)
  }
}

/** A block. */
class Block extends Callable, StmtSequence, Scope, TBlock {
  /**
   * Gets a local variable declared by this block.
   * For example `local` in `{ | param; local| puts param }`.
   */
  LocalVariableWriteAccess getALocalVariable() { result = this.getLocalVariable(_) }

  /**
   * Gets the `n`th local variable declared by this block.
   * For example `local` in `{ | param; local| puts param }`.
   */
  LocalVariableWriteAccess getLocalVariable(int n) { none() }

  override AstNode getAChild(string pred) {
    result = Callable.super.getAChild(pred)
    or
    result = StmtSequence.super.getAChild(pred)
    or
    pred = "getLocalVariable" and result = this.getLocalVariable(_)
  }
}

/** A block enclosed within `do` and `end`. */
class DoBlock extends Block, BodyStmt, TDoBlock {
  private Ruby::DoBlock g;

  DoBlock() { this = TDoBlock(g) }

  final override LocalVariableWriteAccess getLocalVariable(int n) {
    toGenerated(result) = g.getParameters().getLocals(n)
  }

  final override Parameter getParameter(int n) {
    toGenerated(result) = g.getParameters().getChild(n)
  }

  final override string toString() { result = "do ... end" }

  final override AstNode getAChild(string pred) {
    result = Block.super.getAChild(pred)
    or
    result = BodyStmt.super.getAChild(pred)
  }

  final override string getAPrimaryQlClass() { result = "DoBlock" }
}

/**
 * A block defined using curly braces, e.g. in the following code:
 * ```rb
 * names.each { |name| puts name }
 * ```
 */
class BraceBlock extends Block, TBraceBlock {
  final override string toString() { result = "{ ... }" }

  final override string getAPrimaryQlClass() { result = "BraceBlock" }
}
