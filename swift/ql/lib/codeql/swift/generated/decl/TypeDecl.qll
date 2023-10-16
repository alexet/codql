// generated by codegen/codegen.py
private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.type.Type
import codeql.swift.elements.decl.ValueDecl

module Generated {
  class TypeDecl extends Synth::TTypeDecl, ValueDecl {
    /**
     * Gets the name of this type declaration.
     */
    string getName() { result = Synth::convertTypeDeclToRaw(this).(Raw::TypeDecl).getName() }

    /**
     * Gets the `index`th inherited type of this type declaration (0-based).
     *
     * This includes nodes from the "hidden" AST. It can be overridden in subclasses to change the
     * behavior of both the `Immediate` and non-`Immediate` versions.
     */
    Type getImmediateInheritedType(int index) {
      result =
        Synth::convertTypeFromRaw(Synth::convertTypeDeclToRaw(this)
              .(Raw::TypeDecl)
              .getInheritedType(index))
    }

    /**
     * Gets the `index`th inherited type of this type declaration (0-based).
     *
     * This only returns the types effectively appearing in the declaration. In particular it
     * will not resolve `TypeAliasDecl`s or consider base types added by extensions.
     */
    final Type getInheritedType(int index) {
      exists(Type immediate |
        immediate = this.getImmediateInheritedType(index) and
        result = immediate.resolve()
      )
    }

    /**
     * Gets any of the inherited types of this type declaration.
     */
    final Type getAnInheritedType() { result = this.getInheritedType(_) }

    /**
     * Gets the number of inherited types of this type declaration.
     */
    final int getNumberOfInheritedTypes() {
      result = count(int i | exists(this.getInheritedType(i)))
    }
  }
}
