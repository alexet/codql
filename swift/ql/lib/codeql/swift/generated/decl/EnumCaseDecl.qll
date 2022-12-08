// generated by codegen/codegen.py
private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.decl.Decl
import codeql.swift.elements.decl.EnumElementDecl

module Generated {
  class EnumCaseDecl extends Synth::TEnumCaseDecl, Decl {
    override string getAPrimaryQlClass() { result = "EnumCaseDecl" }

    /**
     * Gets the `index`th element of this enum case declaration (0-based).
     *
     * This includes nodes from the "hidden" AST. It can be overridden in subclasses to change the
     * behavior of both the `Immediate` and non-`Immediate` versions.
     */
    EnumElementDecl getImmediateElement(int index) {
      result =
        Synth::convertEnumElementDeclFromRaw(Synth::convertEnumCaseDeclToRaw(this)
              .(Raw::EnumCaseDecl)
              .getElement(index))
    }

    /**
     * Gets the `index`th element of this enum case declaration (0-based).
     */
    final EnumElementDecl getElement(int index) { result = getImmediateElement(index).resolve() }

    /**
     * Gets any of the elements of this enum case declaration.
     */
    final EnumElementDecl getAnElement() { result = getElement(_) }

    /**
     * Gets the number of elements of this enum case declaration.
     */
    final int getNumberOfElements() { result = count(int i | exists(getElement(i))) }
  }
}
