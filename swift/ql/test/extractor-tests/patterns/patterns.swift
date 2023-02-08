func basic_patterns() {
    var an_int = 42
    var a_string: String = "here"
    let (x, y, z) = (1, 2, 3)
    let _ = "any"
    let (_) = "paren"
}

func switch_patterns() {
    let point = (1, 2)
    switch point {
    case let (xx, yy): "binding"
    }

    switch 3 {
    case 1 + 2: "expr"
    case _: ""
    }

    enum Foo {
        case bar, baz(Int, String)
    }

    let v: Foo = .bar

    switch v {
    case .bar: "bar"
    case let .baz(i, s): i
    }

    let w: Int? = nil

    switch w {
    case let n?: n
    case _: "none"
    }

    let a: Any = "any"

    switch a {
    case is Int: "is pattern"
    case let x as String: "as pattern"
    case _: "other"
    }

    let b = true

    switch b {
    case true: "true"
    case false: "false"
    }
}

func bound_and_unbound() {
    let a = 1, b = 2, c: Int = 3

    if let (a, b, c) = Optional.some((a, b, c)) { _ = (a, c) }
    if case (a, let b, let c) = (a, b, c) { _ = (b) }

    switch a {
        case c: "equals c"
        case let c: "binds c"
        default: "default"
    }
}
