package scala.util
package deco


import language.experimental.captureChecking

import caps.ucap
import caps.unsafe.unsafeAssumePure
import annotation.unchecked.uncheckedCaptures


object boundary:

  opaque type Label[-R] = Boundary

  def apply[R](body: Label[R]^ ?=> R): R = boundaryImpl(body)
  
  opaque type Continuation[-A, +R] = ContinuationState

  def suspend[A, R](handler: Continuation[A, R]^{ucap} => R)(using Label[R]^): A = suspendImpl(handler)
  
  extension [A, R](cont: Continuation[A, R]^{ucap})
    def resume(value: A): R = resumeImpl(cont.unsafeAssumePure, value)

  // ------

  import _stack.*
  import compiletime.erasedValue

  private transparent inline def defaultValue[T]: T =
    inline erasedValue[T] match
      case _: Byte => (0: Byte).asInstanceOf[T]
      case _: Char => (0: Char).asInstanceOf[T]
      case _: Short => (0: Short).asInstanceOf[T]
      case _: Int => (0).asInstanceOf[T]
      case _: Long => (0L).asInstanceOf[T]
      case _: Float => (0.0f).asInstanceOf[T]
      case _: Double => (0.0d).asInstanceOf[T]
      case _: Boolean => (false).asInstanceOf[T]
      case _: Unit => (()).asInstanceOf[T]
      case _ => (null).asInstanceOf[T]

  private type Stack = HandledSegmentedStack
  
  private final class Prompt
  private class Boundary(val prompt: Prompt, var handle: Stack#Handle | Null)
  private class ContinuationState(val stack: Stack, var resumed: Boolean)

  // state
  private var stack: Stack = new Stack()
  var _suspending: Boolean = false
  private var suspending_label: ((Label[Any]^) | Null) @uncheckedCaptures = null
  private var suspending_handler: ((Continuation[Any, Any] => Any) | Null) @uncheckedCaptures = null
  var _result: Any = null
  private var installed: Boolean = false

  def _reset(): Unit = 
    stack = new Stack()
    _suspending = false
    suspending_label = null
    suspending_handler = null
    _result = null
    installed = false

  def _pushFrame(frame: Frame): Unit = stack.pushFrame(frame)

  // impls
  private inline def boundaryImpl[R](body: Label[R] ?=> R): R =
    val prompt = new Prompt()
    val label = new Boundary(prompt, null)
    //println(s"boundary $prompt: enter")
    val res = body(using label)
    if _suspending then
      label.handle = stack.pushPrompt()
      //if suspending_label == null then
      //  // resuming continuation
      //  //println(s"boundary $prompt: catched resumption")
      //  val cont = stack
      //  stack = new Stack()
      //  _suspending = false
      //  trampoline[R](cont, false)
      //else
      if !installed && suspending_label.prompt == prompt then
        //println(s"boundary $prompt: catched suspension")
        val cont = stack
        stack = new Stack()
        _suspending = false
        trampoline[R](cont, true)
      else
        //println(s"boundary $prompt: forward")
        defaultValue[R]
    else
      res

  private inline def suspendImpl[A, R](handler: Continuation[A, R] => R)(using label: Label[R]): A =
    //println(s"suspend: suspending to ${label.prompt}")
    _suspending = true
    suspending_label = label
    suspending_handler = handler
    defaultValue[A]

  private inline def resumeImpl[A, R](cont: Continuation[A, R], value: A): R =
    //println(s"resume: resuming with $value")
    //cont.print()
    if cont.resumed then
      throw new UnsupportedOperationException("continuation cannot be resumed multiple times")
    cont.resumed = true
    _result = value
    if !installed then
      //println(s"resume: outer resumption, installing trampoline")
      trampoline[R](cont.stack, false)
    else
      //println(s"resume: inner resumption, returning")
      _suspending = true
      suspending_label = null
      stack = cont.stack
      defaultValue[R]


  private def trampoline[R](cont: Stack, resuming: Boolean): R =
    installed = true
    var ownStack: Stack = new Stack()
    var nextFrame: (Frame, Stack#Handle) | Null = null
    var toResume: Stack | Null = null

    //println(s"trampoline: installing, resuming = $resuming")
    if resuming then
      toResume = cont
    else
      ownStack = cont
      nextFrame = ownStack.popFrame()

    while toResume != null || nextFrame != null do
      var res: R = defaultValue[R]
      if toResume != null then
        //println(s"trampoline: execute resumption")
        val continuationState = new ContinuationState(toResume, false)
        res = suspending_handler(continuationState).asInstanceOf[R]
        toResume = null
      else
        //println(s"trampoline: execute frame")
        res = nextFrame._1.apply().asInstanceOf[R]
      if _suspending then
        val stackPrompt = stack.pushPrompt()
        stack.prepend(ownStack)
        if suspending_label == null then
          //println(s"trampoline: catched resumption")
          // we are resuming
          ownStack = stack
          stack = new Stack()
          _suspending = false
          //ownStack.print()
          nextFrame = ownStack.popFrame()
        else if suspending_label.handle != null then
          //println(s"trampoline: catched suspension ${suspending_label.prompt}")
          // we are suspending and we own the slice of the stack
          if nextFrame != null && suspending_label.handle == nextFrame._2 then
            // targetting the prompt we just popped, need to patch it with new one
            suspending_label.handle = stackPrompt
          ownStack = stack
          stack = new Stack()
          _suspending = false
          val staticOwnStack = ownStack
          toResume = staticOwnStack.splitByHandle(suspending_label.handle.asInstanceOf[staticOwnStack.Handle])
        else
          //println(s"trampoline: forward suspension")
          installed = false
          return defaultValue[R]
      else
        //println(s"trampoline: next frame")
        _result = res
        _suspending = false
        nextFrame = ownStack.popFrame()

    //println(s"trampoline: completed")
    installed = false
    _result.asInstanceOf[R]
