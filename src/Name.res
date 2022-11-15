type rec lambda = 
  | Var(string)
  | Fn(string, lambda)
  | App(lambda, lambda)

let print_lambda = l => {
  let print_paren = (b, s) => {
    if b { "(" ++ s ++ ")" } else { s }
  }
  let rec go = (l, p) => {
    switch l {
      | Var(x) => x
      | Fn(x, a) => print_paren(p>0, "fun " ++ x ++ " -> " ++ go(a, 0))
      | App(a, b) => print_paren(p>1, go(a, 1) ++ " " ++ go(b, 2))

    }
  }
  go(l, 0)
}

// v must be closed. a[v/x]
let rec subst = (x, v, a) => {
  switch a {
    | Var(y) => if x == y { v } else { a }
    | Fn(y, b) => if x == y { a } else { Fn(y, subst(x, v, b)) }
    | App(b, c) => App(subst(x, v, b), subst(x, v, c))
  }
}

let rename = (t, old, new) => {
  let rec go = (t) => {
    switch t {
    | Var(x) => if x == old { Var(new) } else { Var(x) }
    | Fn(x, a) => if x == old { Fn(new, go(a)) } else {Fn(x, go(a))}
    | App(a, b) => App(go(a), go(b))
    }
  }
  go(t)
}

let id = Fn("x", Var("x"))
// fun x -> y x
let t = Fn("x", App(Var("y"), Var("x")))
Js.Console.log(print_lambda(t))
Js.Console.log(print_lambda(rename(t, "x", "z")))

// fun x -> fun y -> (fun x -> x) x y
let t = Fn("x", Fn("y", App(App(Fn("x", Var("x")), Var("x")), Var("y"))))
Js.Console.log(print_lambda(t))
Js.Console.log(print_lambda(rename(t, "x", "z")))

let fresh_name = () => {
  assert false
}

// t[u/x] where u might have free variables
let rec subst = (t, x, u) => {
  switch t {
  | Var(y) => if x == y { u } else { t }
  | Fn(y, b) => if x == y { t } else {
    let y' = fresh_name ()
    let b' = rename(b, y, y')
    Fn(y', subst(b', x, u)) 
  }
  | App(a, b) => App(subst(a, x, u), subst(b, x, u))
  }
}

module Debru = {
  type rec lambda = 
  | Var(int)
  | Fn(lambda) // for printing only
  | App(lambda, lambda)


  // Var(j) becomes Var(i+j) if j >= d
  let rec shift_aux = (i, d, u) => {
    switch u {
    | Var(j) => { if j >= d { Var(i+j) } else { u } }
    | Fn(b) => Fn(shift_aux(i, d+1, b))
    | App(a, b) => 
        App(shift_aux(i, d, a), shift_aux(i, d, b))
    }
  }
  let shift = (i, u) => shift_aux(i, 0, u)

  // t[u/i]: use u to replace Var(i) in term t
  let rec subst = (t, i, u) => {
    switch t {
    | Var(j) => if j == i { u } else { t }
    | Fn(b) => Fn(subst(b, i+1, shift(1, u)))
    | App(a, b) => App(subst(a, i, u), subst(b, i, u))
    }
  }
  
  // Homework: implement the complete interpreter
  let eval = (t: lambda) => {
    assert false
  }

}

// Homework: support let
module DebruLet = {
  type rec lambda = 
  | Var (int)
  | App (lambda, lambda)
  | Fun (lambda)
  | Let (lambda, lambda)

  let eval = (t: lambda) => {
    assert false
  }
}