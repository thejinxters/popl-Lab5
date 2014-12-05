import org.scalatest._
import jsy.lab5.ast._
import Lab5._

class Lab5Spec extends FlatSpec {
  
  "mapFirstDoWith" should "map the first element where f returns Some" in {
     val l1 = List(1, 2, -3, 4, -5)
     val gold1 = List(1, 2, 3, 4, -5)
     def dowith[W]: DoWith[W,List[Int]] = mapFirstWith[W,Int] { (i: Int) => if (i < 0) Some(doreturn(-i)) else None } (l1)
     assertResult((true,gold1)) { dowith(true) }
     assertResult((42,gold1)) { dowith(42) }
  }

  //---------------------------------------------------
  //Typing Tests

  "TypeNumber" should "type to number" in {
    assertResult(TNumber) {
      typeInfer(Map(), N(42))
    }
  }

  "TypeIf" should "ensure branches have same type" in {
    assertResult(TNumber) {
      typeInfer(Map(),
        If(B(false), N(42), N(47)))
    }
    intercept[StaticTypeError] {
      typeInfer(Map(),
        If(B(false), N(42), S("abc")))
    }
  }

  "TypeAssign" should "type an assignment" in {
    // var x = 42; x = 47
    assertResult(TNumber) {
      typeInfer(Map(),
        Decl(MVar, "x", N(42),
          Assign(Var("x"), N(47))))
    }
    // var x = 42; x = "foo"
    intercept[StaticTypeError] {
      typeInfer(Map(),
        Decl(MVar, "x", N(42),
          Assign(Var("x"), S("foo"))))
    }
  }

  //---------------------------------------------------
  //Do Tests

  "DoNeg" should "negate values" in {
    val e = Unary(Neg, N(42))
    val (mp:Mem, ep: Expr) = step(e)(Mem.empty)
    assert(mp.isEmpty)
    assertResult(N(-42)) { ep }
  }

  "DoNot" should "not values" in {
    val e = Unary(Not, B(true))
    val (mp:Mem, ep: Expr) = step(e)(Mem.empty)
    assert(mp.isEmpty)
    assertResult(B(false)) { ep }
  }

  "DoSeq" should "produce second element in sequence" in {
    val e = Binary(Seq, N(1), Binary(Plus, N(2), N(3)))
    val (mp:Mem, ep: Expr) = step(e)(Mem.empty)
    assertResult(Binary(Plus, N(2), N(3))) { ep }
  }

  "DoArith" should "add two numbers" in {

  }

  "DoPlusString" should "add two strings" in {

  }

  "DoInequalityNumber" should "compare two numbers" in {

  }

  "DoInequalityString" should "compare two strings" in {

  }

  "DoEquality" should "determine if two values are equal or not" in {

  }

  "DoAndTrue" should "return value of second value" in {

  }

  "DoAndFalse" should "return false" in {

  }

  "DoOrTrue" should "return true" in {

  }

  "DoOrFalse" should "return second value" in {

  }

  "DoObject" should "access an object in memory" in {

  }

  "DoGetField" should "access a field from an object in memory" in {
    val setup = Obj(Map("a" -> N(42), "b" -> N(47)))
    val (m:Mem, addr: A) = step(setup)(Mem.empty)
    val e = GetField(addr, "b")
    val (mp, ep: Expr) = step(e)(m)
    assertResult(N(47)) { ep }
  }

  "DoConst" should "declare a constant" in {
    val e = Decl(MConst, "x", N(42), Var("x"))
    val (mp: Mem, ep: Expr) = step(e)(Mem.empty)
    assertResult(N(42)) { ep }
  }

  "Do Var" should "assign a var to mem" in {
    val e = Decl(MVar, "x", N(42), Var("x"))
    val (mp: Mem, ep: Expr) = step(e)(Mem.empty)
    assert(ep match {
      case Unary(Deref, a@A(_)) =>
        // Verify memory correctly references N(42)
        mp.get(a).get == N(42)
      case _ => false
    })
  }

  "DoDeref" should "Dereference memory location" in {
    val e = Decl(MVar, "x", N(42), Assign(Var("x"), N(47)))
    val (mp: Mem, ep: Expr) = step(e)(Mem.empty)
    val aref = ep match{
      case Assign(Unary(Deref, a@A(_)), N(47)) => Some(a)
      case _ => None
    }
    val (mpp, epp: Expr) = step(ep)(mp)
    assertResult(N(47)) {
      mpp get (aref get) get
    }
  }

  "DoAssignVar" should "assign variable to value" in {
    val e = Decl(MVar, "x", N(42), Assign(Var("x"), N(47)))
    val (mp: Mem, ep: Expr) = step(e)(Mem.empty)
    val aref = ep match{
      case Assign(Unary(Deref, a@A(_)), N(47)) => Some(a)
      case _ => None
    }
    val (mpp, epp: Expr) = step(ep)(mp)
    assertResult(N(47)) {epp}
  }


  "DoCall" should "call a function" in {

  }

  "DoCastNull" should "cast null to any interface or object" in {
    val m = Mem.empty
    assertResult((m, Null)) {
      // <{}>null
      step(Unary(Cast(TObj(Map())),
        Null))(m)
    }
    assertResult((m, Null)) {
      // interface Nothing {}; <Nothing>null
      step(Unary(Cast(TInterface("Nothing",TObj(Map()))),
        Null))(m)
    }
  }

  "DoCallName" should "sub its expression" in {
    // (function (name e: number){return e})({{6 * 7}})
    val e = Call(
      Function(None,
        Right((PName, "e", TNumber)), None, Var("e")),
      List(Binary(Times, N(6), N(7))))
    val (_, ep: Expr) = step(e)(Mem.empty)
    assertResult(
      Binary(Times, N(6), N(7))) {
      ep
    }
  }

  //---------------------------------------------------
  //Search Tests

  "SearchCall1" should "step its function" in {
    // (true ? function (n: number) { return n } : null)(42)
    val e = Call(If(B(true),Function(None,Left(List(("n",TNumber))),None,Var("n")),Null),List(N(42)))
    val (_, ep: Expr) = step(e)(Mem.empty)
    assertResult(
      Call(Function(None, Left(List(("n", TNumber))), None, Var("n")), List(N(42)))) {
      ep
    }
  }




}
