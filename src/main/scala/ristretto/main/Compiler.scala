package ristretto.main

object Compiler extends Errors {
  def main(args: Array[String]): Unit = {
    import ristretto.frontend.RistrettoPrettyPrinter
    import ristretto.frontend.Ristretto
    import ristretto.frontend.RistrettoSyntax.{ASTNode, Root}
    import ristretto.drip.DripPrettyPrinter
    import ristretto.perc.PercPrettyPrinter
    import ristretto.asm.AsmPrint
    import org.bitbucket.inkytonik.kiama.util.FileSource
    import java.io._

    if (args.length == 0) {
      println("usage: Compiler options file.r")
      println("options: --print-source")
      println("         --print-ast")
      println("         --print-drip")
      println("         --print-perc")
      println("         --print-asm")
      println("         --print-all")
    }
    else {
      lazy val pretty    = (args contains "--pretty")
      lazy val printAll  = (args contains "--print-all")
      lazy val printSrc  = printAll || (args contains "--print-source")
      lazy val printDrip = printAll || (args contains "--print-drip")
      lazy val printPerc = printAll || (args contains "--print-perc")
      lazy val printAsm0 = printAll || (args contains "--print-pseudo-asm")
      lazy val printAsm  = printAll || (args contains "--print-asm")

      for (arg <- args) {
        if (! arg.startsWith("--") && arg.endsWith(".r")) {
          try {
            val src = FileSource(arg)
            val p = new Ristretto(src, Posns)
            val result = p.pRoot(0)
            if (result.hasValue) {
              result.semanticValue[ASTNode] match {
                case t: Root =>
                  if (printSrc && ! pretty) println(t)
                  if (printSrc && pretty)   println(RistrettoPrettyPrinter.show(t))

                  ristretto.frontend.Typer.typeCheck(t)

                  if (hasErrors) {
                    System.exit(1)
                    return
                  }

                  val d = ristretto.frontend.DripGen.translate(t)

                  if (printDrip && ! pretty) println(d)
                  if (printDrip && pretty)   println(DripPrettyPrinter.show(d))

                  val p = ristretto.drip.PercGen.translate(d)

                  if (printPerc && ! pretty) println(p)
                  if (printPerc && pretty)   println(PercPrettyPrinter.show(p))

                  val a0 = ristretto.perc.AsmGen.translate(p)

                  if (printAsm0 && ! pretty) println(a0)
                  if (printAsm0 && pretty)   AsmPrint.print(System.out, a0)

                  val a = ristretto.asm.RegisterAllocation.regalloc(a0)
//                  val a = ristretto.asm.SuboptimalRegisterAllocation.regalloc(a0)

                  if (printAsm && ! pretty) println(a)
                  if (printAsm && pretty)   AsmPrint.print(System.out, a)

                  val sFile = arg.dropRight(1) + "s"
                  val f = new java.io.PrintStream(new java.io.FileOutputStream(sFile))
                  AsmPrint.print(f, a)
                  f.close

                case _ =>
                  println(p.formatParseError(result.parseError, true))
              }
            }
            else {
              println(p.formatParseError(result.parseError, true))
            }
          }
          catch {
            case e: IOException => println(e.getMessage)
            case e: CompilerError => println("fatal error...aborting")
          }
        }
      }

    }
  }
}
