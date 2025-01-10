// analysis-related logic

package deco.plugin

import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Names.*
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.dotc.ast.tpd.*
import dotty.tools.dotc.core.Types.*
import dotty.tools.dotc.core.Flags.*
import dotty.tools.dotc.report

import dotty.tools.dotc.cc.*


// ---  CAPABILITIES ---

def capturesLabel(tpe: Type)(using Context): Boolean =
  def rec(tpe: Type)(using Context): Boolean =
    tpe.widen match
      case wtpe if wtpe.isRef(library.LabelType) => true
      case wtpe =>
        val boxedArgs = wtpe.argInfos.collect{ case ann: AnnotatedType if ann.isBoxed => ann }
        wtpe.captureSet.elems.filter(_ != wtpe).exists(rec) || boxedArgs.exists(rec)
  rec(tpe)

def capturesCap(tpe: Type)(using Context): Boolean = //tpe.widen.deepCaptureSet.isUniversal
  def rec(tpe: Type)(using Context): Boolean =
    val cs = tpe.widen.captureSet
    if cs.isUniversal then true
    else cs.elems.filter(_ != tpe.widen).exists(rec)
  rec(tpe)

def capturesUnenforcedCap(tpe: Type)(using Context): Boolean =
  def rec(tpe: Type)(using Context): Boolean =
    val cs = tpe.widen.captureSet
    if cs.elems.exists(_.isUnenforcedRootCapability) then true
    else cs.elems.filter(_ != tpe.widen).exists(rec)
  rec(tpe)

def mayCapture(tpe: Type)(using Context): Boolean =
  def rec(tpe: Type)(using Context): Boolean =
    tpe.widen match
      case tr: TypeRef if tr.prefix == NoPrefix => true
      case wtpe =>
        val args = wtpe.argInfos
        args.exists(rec)
  rec(tpe)

def capturesContinuation(tpe: Type)(using Context): Boolean =
  def rec(tpe: Type)(using Context): Boolean =
    tpe.widen match
      case wtpe if wtpe.isRef(library.ContinuationType) => true
      case wtpe =>
        val boxedArgs = wtpe.argInfos.collect{ case ann: AnnotatedType if ann.isBoxed => ann }
        wtpe.captureSet.elems.filter(_ != wtpe).exists(rec) || boxedArgs.exists(rec)
  rec(tpe)


// --- SUSPENSION ---

// returns whether the given method is suspendable regarless of the arguments --> single lane
def isSuspendable(symbol: TermSymbol)(using Context): Boolean =
  laneInfo.single.contains(symbol)

// returns whether the given method is suspendable depending on the arguments --> dual lane
def mayBeSuspendable(symbol: TermSymbol)(using Context): Boolean =
  laneInfo.dual.contains(symbol)

// returns whether is the case that the given call may suspend
def callMaySuspend(tree: Apply)(using Context): Boolean =
  tree.hasAttachment(CallMaySuspend)
  && (!compileScala2Library || tree.fun.symbol.name.toString() != "synchronized")

// returns whether the given method is suspendable when capture checking is not available
def noCaptureCheckingBypass(symbol: TermSymbol)(using Context): Boolean =
  !symbol.isConstructor
  && !symbol.is(Bridge)
  && symbol.asTerm != defn.throwMethod
  && !isFunctionApply(symbol)
  && symbol != library.boundary_apply
  && symbol != library.boundary_suspend
  && symbol != library.Continuation_resume
  && symbol != library.boundary__suspending
  && symbol != library.boundary__pushFrame
  && symbol != library.boundary__result
  && (
    (noCaptureChecking
      && !symbol.owner.isPrimitiveValueClass
      && !symbol.owner.linkedClass.isPrimitiveValueClass
      && !defn.pureMethods.contains(symbol)
      && !defn.ObjectMethods.contains(symbol)
      && !defn.pureSimpleClasses.contains(symbol.owner)
      && symbol.name.toString() != "synchronized"
      /*&& false*/)
    || (compileScala2Library
      //&& !ctx.compilationUnit.needsCaptureChecking
      //&& !symbol.owner.isPrimitiveValueClass
      //&& !symbol.owner.linkedClass.isPrimitiveValueClass
      //&& symbol.name.toString() != "synchronized"
      //&& !defn.pureMethods.contains(symbol)
      //&& !defn.ObjectMethods.contains(symbol)
      //&& !defn.pureSimpleClasses.contains(symbol.owner)
      //&& symbol.name.toString() != "execute"
      //&& symbol.name.startsWith("flatMap")
      && (
        symbol.enclosingClass.flatName.toString().contains("Future")
        || symbol.enclosingClass.flatName.toString().contains("Option")
      )
    )
  )

// returns whether the given tree is a suspension point
def isSuspensionPoint(tree: Tree)(using Context): Boolean = tree match
  case apply @ Apply(fun, args) =>
    val symbol = fun.symbol
    symbol != NoSymbol
    && !symbol.isConstructor
    && symbol.asTerm != defn.throwMethod
    &&
      {
        symbol.asTerm == library.boundary_suspend
        || symbol.asTerm == library.Continuation_resume
        //|| isSuspendable(symbol.asTerm)
        //|| mayBeSuspendable(symbol.asTerm)
        || callMaySuspend(apply)
        || noCaptureCheckingBypass(symbol.asTerm)
        || isFunctionApply(symbol)
      }
  case _ => false

// returns whether the given tree has a sub-tree that is a suspension point
def hasSuspensionPoint(tree: Tree)(using Context): Boolean = tree.existsSubTree(isSuspensionPoint)

// disallow suspension point in the given tree
inline def disallowSuspensionPointIn(tree: Tree)(using Context): Unit =
  if !noCaptureChecking && !compileScala2Library && hasSuspensionPoint(tree) then
    report.error("no suspension points allowed at this location", tree.srcPos)


// ---  MISC ---

// returns whether the given symbol is of an unbox method
def isUnbox(symbol: Symbol)(using Context): Boolean = symbol.name == termName("unbox") && symbol.owner.linkedClass.isPrimitiveValueClass

def isFunctionApply(symbol: Symbol)(using Context): Boolean =
  symbol.exists
  && (defn.isFunctionSymbol(symbol.owner) && (symbol.name == termName("apply") || defn.FunctionSpecializedApplyNames.contains(symbol.name)))
  || symbol.allOverriddenSymbols.exists(isFunctionApply)

// returns the set of symbols of the free identifiers ocurring in the given tree
def idents(tree: Tree)(using Context): Set[TermSymbol] = tree match
  case ident: Ident if ident.symbol.owner == ctx.owner => Set(ident.symbol.asTerm)
  case _: SelectWithSig => ???
  case Select(qualifier, _) => idents(qualifier)
  //case _: This => ???
  //case _: Super => ???
  case Apply(fun, args) => idents(fun) ++ args.map(idents).flatten
  case TypeApply(fun, _) => idents(fun)
  //case _: Literal => ???
  //case _: New => ???
  case Typed(expr, _) => idents(expr)
  case _: NamedArg => ???
  case Assign(lhs, rhs) => idents(lhs) ++ idents(rhs)
  case Block(stats, expr) =>
    stats.foldRight(idents(expr))((stat, acc) => stat match
      case valDef: ValDef => (acc - valDef.symbol.asTerm) ++ idents(valDef.rhs)
      case _ => acc ++ idents(stat)
    )
  case _: InlineIf => ???
  case If(cond, thenp, elsep) => idents(cond) ++ idents(thenp) ++ idents(elsep)
  case Closure(env, _, _) => env.map(idents).flatten.toSet
  case _: InlineMatch => ???
  case Match(selector, cases) => idents(selector) ++ cases.map(kase => idents(kase.guard) ++ idents(kase.body)).flatten  // patterns are integer or string constants
  case _: CaseDef => ???
  case Labeled(_, expr) => idents(expr) 
  case Return(expr, _) => idents(expr)
  case WhileDo(cond, body) => idents(cond) ++ idents(body)
  case Try(expr, cases, finalizer) => idents(expr) ++ cases.map(kase => (idents(kase.guard) ++ idents(kase.body)) -- patVars(kase.pat).map(_.asTerm)).flatten ++ idents(finalizer)
  case SeqLiteral(elems, _) => elems.map(idents).toSet.flatten
  case _: JavaSeqLiteral => ???  // TODO?
  case _: Inlined => ???
  case _: Quote => ???
  case _: Splice => ???
  case _: QuotePattern => ???
  case _: SplicePattern => ???
  case _: Hole => ???
  // type trees
  case _: SingletonTypeTree => ???
  case _: RefinedTypeTree => ???
  case _: AppliedTypeTree => ???
  case _: LambdaTypeTree => ???
  case _: TermLambdaTypeTree => ???
  case _: MatchTypeTree => ???
  case _: ByNameTypeTree => ???
  case _: TypeBoundsTree => ???
  // pattern trees
  case _: Bind => ???
  case _: Alternative => ???
  case _: UnApply => ???
  case _: ValDef => ???
  case _: DefDef => ???
  case _: TypeDef => ???
  case _: Template => ???
  case _: Import => ???
  case _: Export => ???
  case _: PackageDef => ???
  //case _: Annotated => ???
  // case _: Thicket => ???  EmptyTree
  case tree => Set.empty[TermSymbol]
