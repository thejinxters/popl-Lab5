object Lab5 extends jsy.util.JsyApplication {
  import jsy.lab5.ast._
  import jsy.lab5._

  /*
   * CSCI 3155: Lab 5
   * Brandon Mikulka
   *
   * Partner: Daniel Palmer
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   *
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */

  /*** Helper: mapFirst to DoWith ***/

  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](f: A => Option[DoWith[W,A]])(l: List[A]): DoWith[W,List[A]] = l match {
    // If the list is empty, just return the empty list "l"
    case Nil => doreturn(l)
    case h :: t => f(h) match {
      // If not the chosen element recurse and return the DoWith list
      case None => mapFirstWith(f)(t).map { x => h :: x}
      // If "chosen" then just map modified element into the original list and return
      case Some(withhp) => for (x <- withhp) yield x::t  //withhp.map {x => x :: t}
    }
  }

  /*** Casting ***/

  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
    case (TNull, TObj(_)) => true
    case (_, _) if t1 == t2 => true
    // Check if fields from First Object are the same type as fields from second object
    case (TObj(fields1), TObj(fields2)) => {
      //First check to see if all of field 1 is the same as field 2
      val fields1ok = fields1 forall{
        case (field, typ1) => fields2.get(field) match{
          case Some(typ2) => if (castOk(typ1, typ2)) true else false
          case None => true
        }
      }
      //Then check to see if all of field 2 is the same as field 1
      val fields2ok = fields2 forall{
        case (field, typ1) => fields1.get(field) match{
          case Some(typ2) => if (castOk(typ1, typ2)) true else false
          case None => true
        }
      }
      fields1ok && fields2ok
    }
    case (TInterface(tvar, t1p), _) => castOk(typSubstitute(t1p, t1, tvar), t2)
    case (_, TInterface(tvar, t2p)) => castOk(t1, typSubstitute(t2p, t2, tvar))
    case _ => false
  }

  /*** Type Inference ***/

  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  def mut(m: PMode): Mutability = m match {
    case PName => MConst
    case PVar | PRef => MVar
  }

  def typeInfer(env: Map[String,(Mutability,Typ)], e: Expr): Typ = {
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw new StaticTypeError(tgot, e1, e)

    e match {
      case Null => TNull
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) =>
        val (_, t) = env(x)
        t
      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typ(e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match {
          case TNumber => TNumber
          case tgot => err(tgot, e2)
        }
        case TString => typ(e2) match {
          case TString => TString
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match {
          case TNumber => TNumber
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Eq|Ne, e1, e2) => typ(e1) match {
        case t1 if !hasFunctionTyp(t1) => typ(e2) match {
          case t2 if (t1 == t2) => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match {
          case TNumber => TBool
          case tgot => err(tgot, e2)
        }
        case TString => typ(e2) match {
          case TString => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(And|Or, e1, e2) => typ(e1) match {
        case TBool => typ(e2) match {
          case TBool => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Seq, e1, e2) => typ(e1); typ(e2)
      case If(e1, e2, e3) => typ(e1) match {
        case TBool =>
          val (t2, t3) = (typ(e2), typ(e3))
          if (t2 == t3) t2 else err(t3, e3)
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields map { case (f,t) => (f, typ(t)) })
      case GetField(e1, f) => typ(e1) match {
        case TObj(tfields) if (tfields.contains(f)) => tfields(f)
        case tgot => err(tgot, e1)
      }

      case Function(p, paramse, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(rt)) =>
            val tprime = TFunction(paramse, rt)
            env + (f -> (MConst, tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with the parameters.
        val env2 = paramse match {
          // Left side of join --> Params with (String, Type)
          case Left(params) => params.foldLeft(env1) {
            (newEnv, param) => param match {
              case (f, rt) => newEnv + (f -> (MConst, rt) )
              case _ => newEnv
            }
          }
          // Right side of join --> Params with (PMode, String, Type)
          case Right((mode,x,t)) => mode match{
            // Pass by Name
            case PName => env1 + ( x -> (MConst, t) )
            // Pass by Ref or Var
            case PRef | PVar =>  env1 + (x -> (MVar, t))
          }
        }
        // Infer the type of the function body
        val t1 = typeInfer(env2, e1)
        tann foreach { rt => if (rt != t1) err(t1, e1) }
        TFunction(paramse, t1)
      }

      case Call(e1, args) => typ(e1) match {
        case TFunction(Left(params), tret) if params.length == args.length => {
          //TypeCall --> check if each param type matches the arg type
          (params, args).zipped.foreach {
            (x1,x2) => if (x1._2 != typ(x2)) err(typ(x2),x2) else typ(x2)
          }
          tret
        }
        case tgot @ TFunction(Right((mode,_,tparam)), tret) if (args.length == 1) =>
          mode match{
            //TypeCallNameVar --> check against args(0) for argument types
            case PName | PVar => if ( tparam == typ(args(0)) ) tret else err( typ(args(0)), args(0) )
            //TypeCallRef --> us isLExp to determine if it is a lazy expression
            case PRef if isLExpr(args(0)) => if ( tparam == typ(args(0)) ) tret else err( typ(args(0)), args(0) )
            case _ => err(tgot, e1)
          }
        case tgot => err(tgot, e1)
      }

      // TypeDecl --> store var type in env and typeinfer on e2
      case Decl(mut, x, e1, e2) => typeInfer(env + (x -> (mut, typ(e1))), e2)
      case Assign(e1, e2) => e1 match {
        //TypeAssignVar
        case Var(x) if (env(x)._1 == MVar) => if (typ(e1) == typ(e2)) typ(e1) else err(typ(e1), e1)
        //TypeAssignField
        case GetField(e3,f) => typ(e3) match {
          case TObj(tfields) if tfields.contains(f) => if (tfields(f) == typ(e2)) typ(e2) else err(typ(e2), e2)
          case tgot => err(tgot, e1)
        }
        case tgot => err(typ(tgot), e1)
      }
      case Unary(Cast(t1), e1) => if (castOk(typ(e1), t1)) t1 else err(typ(e1), e1)


      /* Should not match: non-source expressions or should have been removed */
      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }

  /*** Small-Step Interpreter ***/

  /* Do the operation for an inequality. */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    ((v1, v2): @unchecked) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case (N(n1), N(n2)) =>
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = substitute(e, esub, x)
    // Call avoid capture to avoid capturing free variables
    val ep: Expr = avoidCapture(freeVars(esub), e)
    ep match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
      case Print(e1) => Print(subst(e1))
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) esub else e
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))
      case Function(p, paramse, retty, e1) =>
        if (p == Some(x)) return ep
        paramse match {
          case Left(params) =>
            // forall returns true if each param is not x
            val subOk = params forall { case (pname,typ) => pname != x }
            if (subOk) Function(p,paramse,retty,substitute(e1, esub, x)) else ep
          case Right((mode, pname, typ)) =>
            if (x != pname) Function(p,paramse,retty,substitute(e1, esub, x)) else ep
        }
      case Call(e1, args) => Call(subst(e1), args map subst)
      case Obj(fields) => Obj(fields map { case (fi,ei) => (fi, subst(ei)) })
      case GetField(e1, f) => GetField(subst(e1), f)
      case Assign(e1, e2) => Assign(subst(e1), subst(e2))
      case InterfaceDecl(tvar, t, e1) => InterfaceDecl(tvar, t, subst(e1))
    }
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))

    /*** Helpers for Call ***/

    def stepIfNotValue(e: Expr): Option[DoWith[Mem,Expr]] = if (isValue(e)) None else Some(step(e))

    /* Check whether or not the argument expression is ready to be applied. */
    def argApplyable(mode: PMode, arg: Expr): Boolean = mode match {
      case PVar => isValue(arg)
      case PName => true
      case PRef => isLValue(arg)
    }

    /*** Body ***/
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => for (m <- doget) yield { println(pretty(m, v1)); Undefined }
      case Unary(Neg, N(n1)) => doreturn( N(- n1) )
      case Unary(Not, B(b1)) => doreturn( B(! b1) )
      case Binary(Seq, v1, e2) if isValue(v1) => doreturn( e2 )
      case Binary(Plus, S(s1), S(s2)) => doreturn( S(s1 + s2) )
      case Binary(Plus, N(n1), N(n2)) => doreturn( N(n1 + n2) )
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(inequalityVal(bop, v1, v2)) )
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(v1 == v2) )
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(v1 != v2) )
      case Binary(And, B(b1), e2) => doreturn( if (b1) e2 else B(false) )
      case Binary(Or, B(b1), e2) => doreturn( if (b1) B(true) else e2 )
      case Binary(Minus, N(n1), N(n2)) => doreturn( N(n1 - n2) )
      case Binary(Times, N(n1), N(n2)) => doreturn( N(n1 * n2) )
      case Binary(Div, N(n1), N(n2)) => doreturn( N(n1 / n2) )
      case If(B(b1), e2, e3) => doreturn( if (b1) e2 else e3 )
      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) =>
        for (a <- Mem.alloc(e)) yield a
      case GetField(a @ A(_), f) =>
        // doget grabs memory, then search memory with mem.get(a) returning an Option
        for (mem <- doget) yield mem.get(a)  match {
            // Check to see if fields exist
            case Some(Obj(fields)) => fields.get(f) match{
              case Some(a) => a
              case None => throw StuckError(e)
          }
          case None => throw StuckError(e)
        }

      case Call(v1, args) if isValue(v1) =>
        def substfun(e1: Expr, p: Option[String]): Expr = p match {
          case None => e1
          case Some(x) => substitute(e1, v1, x)
        }
        (v1, args) match {
          /*** Fill-in the DoCall cases, the SearchCall2, the SearchCallVar, the SearchCallRef  ***/

          case (Function(p,paramse,tann,e1),args)=> paramse match{
            //DoCall -- if normal function
            case Left(params) if params.length == args.length =>
              val e1p = (params, args).zipped.foldLeft(e1) {
                (acc, param) => param match {
                  case ((pname, ptype),arg) => substitute(acc, arg, pname)
                }
              }
              p match {
                // DoCall (anonymous not recursive)
                case None => doreturn(e1p)
                // DoCallRec (sub in function).
                case Some(name) => doreturn(substitute(e1p, v1, name))
              }
            case Right((pmode, pname, ptype)) if args.length == 1 => pmode match{
              // DoCallName -- pass by name
              case PName if args.head != Nil =>
                doreturn(substfun(substitute(e1, args.head, pname), p))
              // DoCallVar -- pass by value
              case PVar if isValue(args.head) =>
                Mem.alloc(args.head) map { a => substfun(substitute(e1, Unary(Deref,a), pname),p)}
              // DoCallRef -- pass by ref
              case PRef if isLValue(args.head) =>
                doreturn(substfun(substitute(e1, args.head, pname), p))
              // SearchCallVar and SearchCallRef
              case PVar | PRef => step(args.head) map { e2 => Call(v1, e2 :: Nil) }

              case _ => throw StuckError(e)
            }
            case _ => throw StuckError(e)
          }
          case _ => throw StuckError(e)
        }

      // DoConst
      case Decl(MConst, x, v1, e2) if isValue(v1) =>
        doreturn(substitute(e2, v1, x))
      // DoVar
      case Decl(MVar, x, v1, e2) if isValue(v1) =>
        Mem.alloc(v1) map { a => substitute(e2, Unary(Deref,a), x)}

      //DoAsignVar
      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        for (_ <- domodify { (m: Mem) => (throw new UnsupportedOperationException): Mem }) yield v

      // DoAssignField
      case Assign(GetField(obj,f), v) if isValue(v) => throw new UnsupportedOperationException

      // DoDeref
      case Unary(Deref, a @ A(_)) => throw new UnsupportedOperationException

      // DocastNull
      case Unary(Cast(t), Null) => doreturn( Null )

      // DoCastObj
      case Unary(Cast(TObj(tfields)), a @ A(_)) => throw new UnsupportedOperationException

      // DoCast
      case Unary(Cast(t), v) if isValue(v) => throw new UnsupportedOperationException


      /* Base Cases: Error Rules */
      /*** Fill-in cases here. ***/

      /* Inductive Cases: Search Rules */
      case Print(e1) =>
        for (e1p <- step(e1)) yield Print(e1p)
      case Unary(uop, e1) =>
        for (e1p <- step(e1)) yield Unary(uop, e1p)
      case Binary(bop, v1, e2) if isValue(v1) =>
        for (e2p <- step(e2)) yield Binary(bop, v1, e2p)
      case Binary(bop, e1, e2) =>
        for (e1p <- step(e1)) yield Binary(bop, e1p, e2)
      case If(e1, e2, e3) =>
        for (e1p <- step(e1)) yield If(e1p, e2, e3)
      case Obj(fields) => fields find { case (_, ei) => !isValue(ei) } match {
        case Some((fi,ei)) =>
          throw new UnsupportedOperationException
        case None => throw StuckError(e)
      }
      case GetField(e1, f) => throw new UnsupportedOperationException

      case Call(e1, args) => throw new UnsupportedOperationException

      case Decl(mut, x, e1, e2) => throw new UnsupportedOperationException

      case Assign(e1, e2) if (!isLValue(e1)) => throw new UnsupportedOperationException

      case Assign(e1, e2) => throw new UnsupportedOperationException

      /*** Fill-in more Search cases here. ***/

      /* Everything else is a stuck error. */
      case _ => throw StuckError(e)
    }
  }

  /*** External Interfaces ***/

  this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(500) // comment this out or set to None to not bound the number of steps.

  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    }
    val t = typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }

  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging.

  case class TerminationError(e: Expr) extends Exception {
    override def toString = Parser.formatErrorMessage(e.pos, "TerminationError", "run out of steps in evaluating " + e)
  }

  def iterateStep(e: Expr): Expr = {
    require(closed(e), "not a closed expression: free variables: %s".format(freeVars(e)) )
    def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
      if (Some(n) == maxSteps) throw TerminationError(e)
      else if (isValue(e)) doreturn( e )
      else {
        for {
          m <- doget[Mem]
          _ = if (debug) { println("Step %s:%n  %s%n  %s".format(n, m, e)) }
          ep <- step(e)
          epp <- loop(ep, n + 1)
        } yield
        epp
      }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val (m,v) = loop(e, 0)(Mem.empty)
    if (debug) {
      println("Result:%n  %s%n  %s".format(m,v))
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(removeInterfaceDecl(jsy.lab5.Parser.parse(s)))

  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }

    val expr =
      handle(None: Option[Expr]) {Some{
        jsy.lab5.Parser.parseFile(file)
      }} getOrElse {
        return
      }

    val exprlowered =
      handle(None: Option[Expr]) {Some{
        removeInterfaceDecl(expr)
      }} getOrElse {
        return
      }

    handle() {
      val t = inferType(exprlowered)
    }

    handle() {
      val v1 = iterateStep(exprlowered)
      println(pretty(v1))
    }
  }

}