package deco.plugin

import dotty.tools.dotc.CompilationUnit
import dotty.tools.dotc.plugins.*
import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Names.*
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.dotc.ast.tpd.*
import dotty.tools.dotc.core.Types.*
import dotty.tools.dotc.core.Flags.*

import dotty.tools.dotc.transform.*
import dotty.tools.dotc.core.DenotTransformers.*
import dotty.tools.dotc.util.*

import dotty.tools.dotc.cc.*


class CheckCapturesWrapperPhase extends CheckCaptures:

  override def newRechecker()(using Context) = CaptureCheckerWrapper(ctx)

  class CaptureCheckerWrapper(ictx: Context) extends CaptureChecker(ictx):

    override def keepType(tree: Tree): Boolean = true

    override def checkUnit(unit: CompilationUnit)(using Context): Unit =
      super.checkUnit(unit)
      extractSuspensionInformation(unit.tpdTree)

    private def extractSuspensionInformation(tree: Tree)(using Context): Unit =

      enum Suspendable:
        case Yes, Maybe, No

      def determineSuspendable(symbol: TermSymbol): Suspendable =
        val paramTypes = symbol.paramSymss.flatten.map(_.info)
        val enclosingClass = symbol.enclosingClass.asClass
        val selfType = enclosingClass.classInfo.selfType
        val captures = capturedVars(symbol)

        if debugInfo then println(s" \\ paramTypes ${paramTypes.map(_.show)}; selfType ${selfType.show}; captures ${captures.show}")

        if paramTypes.exists(capturesLabel) || capturesLabel(selfType) || captures.elems.exists(capturesLabel) then Suspendable.Yes
        else if paramTypes.exists(capturesContinuation) || capturesContinuation(selfType) || captures.elems.exists(capturesContinuation) then Suspendable.Yes
        else if paramTypes.exists(capturesCap) || capturesCap(selfType) || captures.elems.exists(capturesCap) then Suspendable.Maybe
        else if paramTypes.exists(capturesUnenforcedCap) || capturesUnenforcedCap(selfType) || captures.elems.exists(capturesUnenforcedCap) then Suspendable.Maybe
        else if paramTypes.exists(mayCapture) || enclosingClass.typeParams.nonEmpty then Suspendable.Maybe
        else Suspendable.No

      tree.foreachSubTree{
        case defDef: DefDef if !defDef.symbol.isConstructor && !isFunctionApply(defDef.symbol) =>
          val symbol = defDef.symbol.asTerm
          
          if debugInfo then println(s"analyzing method ${symbol.fullName.show}")

          val suspendable =
            if symbol.allOverriddenSymbols.exists(os => determineSuspendable(os.asTerm) == Suspendable.Maybe) then Suspendable.Maybe
            else determineSuspendable(symbol)

          if debugInfo then println(s"- ${suspendable.toString()}")
          assert(suspendable != Suspendable.Yes || symbol.allOverriddenSymbols.forall(os => !os.isDefinedInSource || determineSuspendable(os.asTerm) == Suspendable.Yes))
          assert(compileScala2Library || suspendable != Suspendable.Maybe || symbol.allOverriddenSymbols.forall(os => !os.isDefinedInSource || determineSuspendable(os.asTerm) == Suspendable.Maybe))

          suspendable match
            case Suspendable.Yes =>
              laneInfo.single += (symbol -> NoSymbol)
            case Suspendable.Maybe =>
              laneInfo.dual += (symbol -> NoSymbol)
              laneInfo.dual ++= symbol.allOverriddenSymbols.filter(_.isDefinedInSource).map(_ -> NoSymbol)
            case Suspendable.No => ()
        
        case apply: Apply if apply.fun.symbol.isTerm && !apply.fun.symbol.isConstructor && !isFunctionApply(apply.fun.symbol) && !defn.pureMethods.contains(apply.fun.symbol) =>
          val funSym = apply.fun.symbol.asTerm
          if funSym != library.boundary_suspend && funSym != library.Continuation_resume then
            def getObjectAndMoreArgs(tree: Tree, moreArgs: List[Tree]): (Tree, List[Tree]) = tree match
              case ident: Ident => (ident, moreArgs)
              case Select(qual, _) => (qual, moreArgs)
              case TypeApply(fn, _) => getObjectAndMoreArgs(fn, moreArgs)
              case Apply(fun, args) => getObjectAndMoreArgs(fun, args ++ moreArgs)
              case tree => (tree, moreArgs)

              val (o, ma) = getObjectAndMoreArgs(apply.fun, Nil)
              val types = (o :: ma ::: apply.args).map(arg => arg.getAttachment(Recheck.RecheckedType).getOrElse(arg.tpe))
              val captures = capturedVars(funSym)
            
            if debugInfo then println(s"analyzing call ${apply.show}\n \\ types ${types.map(_.show)}; captures ${captures.show}")
            
            if types.exists(capturesLabel) || captures.elems.exists(capturesLabel)
              || types.exists(capturesContinuation) || captures.elems.exists(capturesContinuation)
              || types.exists(capturesCap) || captures.elems.exists(capturesCap)
              || types.exists(capturesUnenforcedCap) || captures.elems.exists(capturesUnenforcedCap) then
              if debugInfo then println(" --> may suspend")
              apply.putAttachment(CallMaySuspend, ())

        case _ => ()
      }
