/**
 * Contains an abstract class that serves as a Base for the classes that deal with both the AST
 * generated declarations and the compiler generated ones (captures the common patterns).
 */

import csharp
private import experimental.ir.implementation.Opcode
private import experimental.ir.internal.IRUtilities
private import experimental.ir.implementation.internal.OperandTag
private import experimental.ir.implementation.raw.internal.InstructionTag
private import experimental.ir.implementation.raw.internal.TranslatedElement
private import experimental.ir.implementation.raw.internal.TranslatedExpr
private import experimental.ir.implementation.raw.internal.TranslatedInitialization
private import experimental.ir.internal.CSharpType
private import experimental.ir.internal.IRCSharpLanguage as Language

abstract class LocalVariableDeclarationBase extends TranslatedElement {
  override TranslatedElement getChild(int id) { id = 0 and result = this.getInitialization() }

  override Instruction getFirstInstruction() { result = this.getVarAddress() }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CSharpType resultType) {
    tag = InitializerVariableAddressTag() and
    opcode instanceof Opcode::VariableAddress and
    resultType = getTypeForGLValue(this.getVarType())
    or
    this.hasUninitializedInstruction() and
    tag = InitializerStoreTag() and
    opcode instanceof Opcode::Uninitialized and
    resultType = getTypeForPRValue(this.getVarType())
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    (
      tag = InitializerVariableAddressTag() and
      kind instanceof GotoEdge and
      if this.hasUninitializedInstruction()
      then result = this.getInstruction(InitializerStoreTag())
      else result = this.getInitialization().getFirstInstruction()
    )
    or
    this.hasUninitializedInstruction() and
    kind instanceof GotoEdge and
    tag = InitializerStoreTag() and
    (
      result = this.getInitialization().getFirstInstruction()
      or
      not exists(this.getInitialization()) and result = this.getParent().getChildSuccessor(this)
    )
  }

  override Instruction getChildSuccessor(TranslatedElement child) {
    child = this.getInitialization() and result = this.getParent().getChildSuccessor(this)
  }

  override Instruction getInstructionOperand(InstructionTag tag, OperandTag operandTag) {
    this.hasUninitializedInstruction() and
    tag = InitializerStoreTag() and
    operandTag instanceof AddressOperandTag and
    result = this.getVarAddress()
  }

  /**
   * Holds if the declaration should have an `Uninitialized` instruction.
   * Compiler generated elements should override this predicate and
   * make it empty, since we always initialize the vars declared during the
   * desugaring process.
   */
  predicate hasUninitializedInstruction() {
    not exists(this.getInitialization()) or
    this.getInitialization() instanceof TranslatedListInitialization
  }

  Instruction getVarAddress() { result = this.getInstruction(InitializerVariableAddressTag()) }

  /**
   * Gets the declared variable. For compiler generated elements, this
   * should be empty (since we treat temp vars differently).
   */
  abstract LocalVariable getDeclVar();

  /**
   * Gets the type of the declared variable.
   */
  abstract Type getVarType();

  /**
   * Gets the initialization, if there is one.
   * For compiler generated elements we don't treat the initialization
   * as a different step, but do it during the declaration.
   */
  abstract TranslatedElement getInitialization();
}
