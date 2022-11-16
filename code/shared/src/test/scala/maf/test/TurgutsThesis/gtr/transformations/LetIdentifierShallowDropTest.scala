package maf.test.TurgutsThesis.gtr.transformations

import maf.TurgutsThesis.gtr.transformations.LetIdentifierShallowDrop
import maf.language.scheme.{SchemeBegin, SchemeParser}
import org.scalatest.flatspec.AnyFlatSpec

class LetIdentifierShallowDropTest extends AnyFlatSpec {
  "LetIdentifierShallowDrop" should "deep drop a lets identifier" in {
    val programText =
      """(begin
        |  (+ 2 2)
        |  (let ((a 10)
        |        (b 100))
        |    b
        |    (+ b a)
        |    (if #t a 99)))""".stripMargin

    val t: SchemeBegin = SchemeParser.parseProgramText(programText).last.asInstanceOf[SchemeBegin]

    val suggestedTrees = LetIdentifierShallowDrop.transform(t, t.exps(1))

    println(suggestedTrees)

    assert(suggestedTrees.exists(tree => {
      tree.toString equals "(begin (+ 2 2) (let ((a 10)) (if #t a 99)))"
    }))

    assert(suggestedTrees.exists(tree => {
      tree.toString equals "(begin (+ 2 2) (let ((b 100)) b))"
    }))

  }

  "LetIdentifierShallowDrop" should "return empty list for non-let exps" in {
    val programText =
      """(begin
        |  (+ 2 2)
        |  (lambda (a)
        |    (+ 99 a)
        |    (if #t a 99)))""".stripMargin

    val t: SchemeBegin = SchemeParser.parseProgramText(programText).last.asInstanceOf[SchemeBegin]

    val suggestedTrees = LetIdentifierShallowDrop.transform(t, t.exps(1)) //corresponds to lambda exp

    assert(suggestedTrees equals List())
  }
}

