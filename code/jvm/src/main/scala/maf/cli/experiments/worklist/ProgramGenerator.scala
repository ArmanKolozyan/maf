package maf.cli.experiments.worklist

object ProgramGenerator:
    private def defineSingleUpflow(n: Int) = s"""
    |(define (do-$n l) (root l))
    """

    /** Generates a program that has a large upflow of values. */
    def upflow(n: Int): String = s"""
    |(define (root l) 1)
    |${(1 to n).map(defineSingleUpflow).mkString("\n")}
    |${(1 to n).map(i => s"(do-$i (lambda (x) x))").mkString("\n")}
    |${(1 to n).map(i => s"(do-$i (lambda (x) x))").mkString("\n")}
    """.stripMargin

    /** Similar to upflow but also generates a downflow by return the argument */
    def upflow2(n: Int): String = s"""
    |(define (root l) l)
    |${(1 to n).map(defineSingleUpflow).mkString("\n")}
    |${(1 to n).map(i => s"(do-$i (lambda (x) x))").mkString("\n")}
    |${(1 to n).map(i => s"(do-$i (lambda (x) x))").mkString("\n")}
    """.stripMargin
