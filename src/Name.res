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
  | Fn(lambda) 
  | App(lambda, lambda)

  let rec toString = (t: lambda): string => switch t {
  | Var(i) => Js.Int.toString(i)
  | Fn(b) => "(λ." ++ toString(b) ++")"
  | App(m, n) => "(" ++ toString(m) ++" " ++ toString(n) ++ ")"
  }

  let print_lambda = l => {
    let print_paren = (b, s) => {
      if b { "(" ++ s ++ ")" } else { s }
    }
    let rec go = (l, p) => {
      switch l {
        | Var(x) => Js.Int.toString(x)
        | Fn(a) => print_paren(p>0, "fun -> " ++ go(a, 0))
        | App(a, b) => print_paren(p>1, go(a, 1) ++ " " ++ go(b, 2))

      }
    }
    go(l, 0)
  }


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
    let r = switch t {
    | Var(j) => if j == i { u } else { t }
    | Fn(b) => Fn(subst(b, i+1, shift(1, u)))
    | App(a, b) => App(subst(a, i, u), subst(b, i, u))
    }
    // Js.log("Subst by replace " ++ print_lambda(Var(i)) ++ " to " ++ print_lambda(u) ++ " on " ++ print_lambda(t) ++ " gets " ++ print_lambda(r))
    r
  }
  
  // Homework: implement the complete interpreter
  let eval = (t: lambda) => {
    let rec evalWithBindIndex = (t:lambda, bi:int) => {
      let r = switch t {
      | Var(_) => t
      | Fn(b) => Fn(evalWithBindIndex(b, bi+1))
      | App(f, arg) => {
        switch evalWithBindIndex(f,bi) {
        | Fn(b) => {
          let va = evalWithBindIndex(arg, bi)
          let va_shifted = shift(1,va)
          let b_substed = subst(b, 0, va_shifted)
          let b_substed_deshifted = shift(-1, b_substed)
          // Js.log("b = " ++ print_lambda(b))
          // Js.log("va = " ++ print_lambda(va) ++ " shifted to " ++ print_lambda(va_shifted))
          // Js.log("bi = " ++ print_lambda(Var(bi)))
          // Js.log("subst gets: " ++ print_lambda(b_substed)) 
          // Js.log("deshift gets: " ++ print_lambda(b_substed_deshifted))
          // Js.log("On bond index " ++ Js.Int.toString(bi) ++ " : " ++ "Apply " ++ print_lambda(f) ++ " on " ++ print_lambda(arg) ++ " gets " ++ print_lambda(b_substed_deshifted))
          evalWithBindIndex(b_substed_deshifted, bi)
        }
        | k => App(k, evalWithBindIndex(arg, bi))
        }
      }
      }
      // Js.log("On bond index " ++ Js.Int.toString(bi) ++ " : " ++print_lambda(t) ++ " evals to " ++ print_lambda(r))
      r
    }
    evalWithBindIndex(t, 0)
  }
}

module DebruTest = {
  open! Debru

  let id = Fn(Var(0))
  let trueB = Fn(Fn(Var(1)))
  let falseB = Fn(Fn(Var(0)))
  let zero = Fn(Fn(Var(0)))
  let one = Fn(Fn(App(Var(1),Var(0))))
  let succ = Fn(Fn(Fn(App(Var(1),App(App(Var(2),Var(1)),Var(0))))))
  let pair = Fn(Fn(Fn(App(App(Var(0),Var(2)),Var(1)))))
  let fst = Fn(App(Var(0),trueB))
  let snd = Fn(App(Var(0),falseB))
  let pred = 
  Fn(App(
    fst,App(
      App(
        Var(0),
        Fn(App(
          App(pair,App(snd,Var(0))),
          App(succ,App(snd,Var(0)))))),
      App(App(pair,zero),zero))))
  let toChurchNumB = (n : int) => {
    let rec helper = (n: int, churchNumB: lambda) : lambda => 
      if n < 0 {assert false}
      else {
        switch n {
        | 0 => churchNumB 
        | _ => helper(n-1, App(succ, churchNumB))
        }
      }
    helper(n, zero)
  }

  let test = () => {
    // Js.log(print_lambda(id))
    // Js.log(print_lambda(trueB))
    // Js.log(print_lambda(falseB))
    // Js.log(print_lambda(zero))
    // Js.log(print_lambda(one))
    // Js.log(print_lambda(fst))
    // Js.log(print_lambda(snd))
    // Js.log(print_lambda(succ))
    // Js.log(print_lambda(toChurchNumB(9)))
    // Js.log(print_lambda(eval(toChurchNumB(9))))
    // let pair2_1 = App(App(pair,toChurchNumB(2)),toChurchNumB(1))
    // Js.log(print_lambda(eval(pair2_1)))
    // Js.log(print_lambda(eval(App(fst,pair2_1))))
    // Js.log(print_lambda(eval(App(snd,pair2_1))))
    // Js.log(print_lambda(App(pred,toChurchNumB(1))))
    Js.log(print_lambda(eval(App(pred,toChurchNumB(8)))))
    // let examp = Fn(App(Fn(App(App(pair,Var(1)),Var(0))),Var(3)))
    // Js.log(print_lambda(examp))
    // Js.log(print_lambda(eval(examp)))
  }
}

let _ = DebruTest.test()

// Homework: support let
module DebruLet = {
  type rec lambda = 
  | Var (int)
  | App (lambda, lambda)
  | Fn (lambda)
  | Let (lambda, lambda)

  let rec toString = (t: lambda): string => switch t {
  | Var(i) => Js.Int.toString(i)
  | Fn(b) => "(λ." ++ toString(b) ++")"
  | App(m, n) => "(" ++ toString(m) ++" " ++ toString(n) ++ ")"
  | Let(l, b) => "(" ++ toString(l) ++ "->" ++ toString(b) ++ ")"
  }

  let print_lambda = l => {
    let print_paren = (b, s) => {
      if b { "(" ++ s ++ ")" } else { s }
    }
    let rec go = (l, p) => {
      switch l {
        | Var(x) => Js.Int.toString(x)
        | Fn(a) => print_paren(p>0, "fun -> " ++ go(a, 0))
        | App(a, b) => print_paren(p>1, go(a, 1) ++ " " ++ go(b, 2))
        | Let(l, b) => print_paren(p>1, "let " ++ go(l,1) ++ " in " ++ go(b, 2))
      }
    }
    go(l, 0)
  }


  // Var(j) becomes Var(i+j) if j >= d
  let rec shift_aux = (i, d, u) => {
    switch u {
    | Var(j) => { if j >= d { Var(i+j) } else { u } }
    | Fn(b) => Fn(shift_aux(i, d+1, b))
    | App(a, b) => 
        App(shift_aux(i, d, a), shift_aux(i, d, b))
    | Let(l, b) => shift_aux(i,d,App(Fn(b),l))
    }
  }
  let shift = (i, u) => shift_aux(i, 0, u)

  // t[u/i]: use u to replace Var(i) in term t
  let rec subst = (t, i, u) => {
    let r = switch t {
    | Var(j) => if j == i { u } else { t }
    | Fn(b) => Fn(subst(b, i+1, shift(1, u)))
    | App(a, b) => App(subst(a, i, u), subst(b, i, u))
    | Let(l, b) => subst(App(Fn(b),l),i,u)
    }
    // Js.log("Subst by replace " ++ print_lambda(Var(i)) ++ " to " ++ print_lambda(u) ++ " on " ++ print_lambda(t) ++ " gets " ++ print_lambda(r))
    r
  }
 
// eval Let(x, exp1, exp2) == eval App(Fn(x,exp2),exp1)
// eval Let(l1, l2) == eval App((lambda.l2),l1)
  let eval = (t: lambda) => {
    let rec evalWithBindIndex = (t:lambda, bi:int) => {
      let r = switch t {
      | Var(_) => t
      | Fn(b) => Fn(evalWithBindIndex(b, bi+1))
      | Let(loc, body) => evalWithBindIndex(App(Fn(body),loc),bi)
      | App(f, arg) => {
        switch evalWithBindIndex(f,bi) {
        | Fn(b) => {
          let va = evalWithBindIndex(arg, bi)
          let va_shifted = shift(1,va)
          let b_substed = subst(b, 0, va_shifted)
          let b_substed_deshifted = shift(-1, b_substed)
          // Js.log("b = " ++ print_lambda(b))
          // Js.log("va = " ++ print_lambda(va) ++ " shifted to " ++ print_lambda(va_shifted))
          // Js.log("bi = " ++ print_lambda(Var(bi)))
          // Js.log("subst gets: " ++ print_lambda(b_substed)) 
          // Js.log("deshift gets: " ++ print_lambda(b_substed_deshifted))
          // Js.log("On bond index " ++ Js.Int.toString(bi) ++ " : " ++ "Apply " ++ print_lambda(f) ++ " on " ++ print_lambda(arg) ++ " gets " ++ print_lambda(b_substed_deshifted))
          evalWithBindIndex(b_substed_deshifted, bi)
        }
        | k => App(k, evalWithBindIndex(arg, bi))
        }
      }
      }
      // Js.log("On bond index " ++ Js.Int.toString(bi) ++ " : " ++print_lambda(t) ++ " evals to " ++ print_lambda(r))
      r
    }
    evalWithBindIndex(t, 0)
  }
}

module DebruLetTest = {
  open! DebruLet


  let id = Fn(Var(0))
  let trueB = Fn(Fn(Var(1)))
  let falseB = Fn(Fn(Var(0)))
  let zero = Fn(Fn(Var(0)))
  let one = Fn(Fn(App(Var(1),Var(0))))
  let succ = Fn(Fn(Fn(App(Var(1),App(App(Var(2),Var(1)),Var(0))))))
  let pair = Fn(Fn(Fn(App(App(Var(0),Var(2)),Var(1)))))
  let fst = Fn(App(Var(0),trueB))
  let snd = Fn(App(Var(0),falseB))
  let pred = Let(
                Fn(App(
                  App(pair,App(snd,Var(0))),
                  App(succ,App(snd,Var(0))))),
                Let(
                  App(App(pair,zero),zero),
                  Fn(App(fst,App(App(Var(0),Var(2)),Var(1))))
          ))
  let toChurchNumB = (n : int) => {
    let rec helper = (n: int, churchNumB: lambda) : lambda => 
      if n < 0 {assert false}
      else {
        switch n {
        | 0 => churchNumB 
        | _ => helper(n-1, App(succ, churchNumB))
        }
      }
    helper(n, zero)
  }

  let test = () => {
    // Js.log(print_lambda(id))
    // Js.log(print_lambda(trueB))
    // Js.log(print_lambda(falseB))
    // Js.log(print_lambda(zero))
    // Js.log(print_lambda(one))
    // Js.log(print_lambda(fst))
    // Js.log(print_lambda(snd))
    // Js.log(print_lambda(succ))
    // Js.log(print_lambda(toChurchNumB(9)))
    // Js.log(print_lambda(eval(toChurchNumB(9))))
    // let pair2_1 = App(App(pair,toChurchNumB(2)),toChurchNumB(1))
    // Js.log(print_lambda(eval(pair2_1)))
    // Js.log(print_lambda(eval(App(fst,pair2_1))))
    // Js.log(print_lambda(eval(App(snd,pair2_1))))
    // Js.log(print_lambda(App(pred,toChurchNumB(1))))
    // Js.log(print_lambda(eval(App(pred,toChurchNumB(8)))))
    Js.log(print_lambda(eval(Let(pred,App(Var(0),toChurchNumB(8))))))
    // let examp = Fn(App(Fn(App(App(pair,Var(1)),Var(0))),Var(3)))
    // Js.log(print_lambda(examp))
    // Js.log(print_lambda(eval(examp)))
  }
}

let _ = DebruLetTest.test()