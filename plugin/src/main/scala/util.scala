// utils

package deco.plugin

import dotty.tools.dotc.core.Constants.*
import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Names.*
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.dotc.ast.tpd.*
import dotty.tools.dotc.core.Types.*
import dotty.tools.dotc.core.Flags.*
import dotty.tools.dotc.transform.Erasure.Boxing
import dotty.tools.dotc.util.Property


val suspendableSuffix = "$suspendable"

// --- LIBRARY ---

object library:

  def decoPackage(using Context): Symbol = requiredPackage("scala.util.deco")
  def boundaryModule(using Context): TermSymbol = requiredModule("scala.util.deco.boundary")
  def boundary_apply(using Context): TermSymbol = boundaryModule.requiredMethod("apply")
  def boundary_suspend(using Context): TermSymbol = boundaryModule.requiredMethod("suspend")
  def Continuation_resume(using Context): TermSymbol = boundaryModule.requiredMethod("resume")

  def boundary__pushFrame(using Context): TermSymbol = boundaryModule.requiredMethod("_pushFrame")
  def boundary__suspending(using Context): TermSymbol = boundaryModule.requiredValue("_suspending")
  def boundary__result(using Context): TermSymbol = boundaryModule.requiredValue("_result")

  def LabelType(using Context): TypeSymbol = boundaryModule.requiredType("Label")
  def ContinuationType(using Context): TypeSymbol = boundaryModule.requiredType("Continuation")


// --- MISC ---

// generates unique names appending '_N' given a prefix
private class UniqueNamer:
  private val counts: collection.mutable.Map[String, Int] = collection.mutable.Map.empty[String, Int]
  def fresh(name: String): String =
    val res = s"${name}_${counts.getOrElseUpdate(name, 1)}"
    counts.update(name, counts(name) + 1)
    res

inline def identFor(symbol: TermSymbol)(using Context): Tree = ref(symbol)

// --- TREE BUILDERS ---

inline def suspending(using Context): Tree = identFor(library.boundary__suspending).appliedToNone

// we need to unbox!
inline def resultAs(tpe: Type)(using Context): Tree =
  if tpe.isPrimitiveValueType
  then
    val cls = tpe.classSymbol.asClass
    if cls == defn.UnitClass
    then unitLiteral
    else identFor(cls.linkedClass.info.member(termName("unbox")).symbol.asTerm).appliedTo(identFor(library.boundary__result).appliedToNone)
  else
    identFor(library.boundary__result).appliedToNone.select(termName("asInstanceOf")).appliedToType(tpe)

inline def pushLiftedClosure(closure: Closure)(using Context): Tree =  identFor(library.boundary__pushFrame).appliedTo(Typed(closure, ref(defn.Function0)))

// --- LANE INFORMATION ---

val CallMaySuspend: Property.StickyKey[Unit] = Property.StickyKey()

case class LaneInfo(single: collection.mutable.Map[Symbol, Symbol], dual: collection.mutable.Map[Symbol, Symbol])
val laneInfo = LaneInfo(collection.mutable.Map.empty[Symbol, Symbol], collection.mutable.Map.empty[Symbol, Symbol])
