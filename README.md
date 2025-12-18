## Files
1. `miniML.ml` 
2. `miniML_with_gc.ml` (with garbage collection, supports call by reference)
3. `typecheckerml.ml` (type checker implementation for subset of miniML) 

## Quick start

1. type `utop` in project root directory 
2. In `utop`, type `#use <"miniML.ml" || "miniML_with_gc.ml" || "typecheckerml.ml">` to load code.
3. write any expression you want and `run` it.

### Example (miniML.ml)

#### Factorial

```ocaml
let test_expr = LETREC ("factorial", "x",
    IF (EQUAL (VAR "x", CONST 0), 
        CONST 1, 
        MUL (CALL (VAR "factorial", 
            SUB (VAR "x", CONST 1)), VAR "x")),
            LETREC ("loop", "n",
                IF (EQUAL (VAR "n", CONST 0),
                    UNIT, 
                    SEQ (PRINT (CALL (VAR "factorial", VAR "n")),
                        CALL (VAR "loop", SUB (VAR "n", CONST 1)))),
                        CALL (VAR "loop", CONST 10)))
```
`> run test_expr;;` in `utop`

#### range

```ocaml
let test_expr = LETREC ("range", "n", 
    IF (EQUAL (VAR "n", CONST 1),
        CONS (CONST 1, NIL),
        CONS (VAR "n", 
            CALL (VAR "range", SUB (VAR "n", CONST 1)))), CALL (VAR "range", CONST 10))
```

`> run test_expr;;`

### Example (miniML_with_gc.ml)

```ocaml
(* ========================================== *)
(* Extreme GC Test: The Cyclic Islands        *)
(* ========================================== *)

(* Program Logic:
   let root = new 0 in           
   (
      let n1 = new 1 in          
      let n2 = new 2 in          
      let self = new 3 in       
      
      (* 1. Create Cycle: n1 <-> n2 *)
      *n1 := n2;
      *n2 := n1;
      
      (* 2. Create Self-Cycle: self -> self *)
      *self := self;
      
      (* 3. Block ends. n1, n2, self go out of scope. *)
      unit
   );
   root                         
*)

let extreme_gc_pgm = 
  LET ("root", NEW (CONST 0),
    SEQ (
      LET ("n1", NEW (CONST 1),
        LET ("n2", NEW (CONST 2),
          LET ("self", NEW (CONST 3),
            SEQ (
              (* n1 points to n2 *)
              STORE (VAR "n1", VAR "n2"),
              SEQ (
                (* n2 points to n1 (Cycle Created!) *)
                STORE (VAR "n2", VAR "n1"),
                SEQ (
                   (* self points to self (Self-Cycle!) *)
                   STORE (VAR "self", VAR "self"),
                   UNIT
                )
              )
            )
          )
        )
      ),
      (* Return root only *)
      VAR "root"
    )
  )
```

compare printed mem size message 

`> run extreme_gc_pgm false true;;` (gc off)

`> run extreme_gc_pgm true true;;` (gc on)


## Reference
Specification I followed

프로그래밍 언어의 원리  (Introduction to Programming Language Principles), 오학주
