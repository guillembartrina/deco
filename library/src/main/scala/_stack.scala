package scala.util
package deco
package _stack


// representation of a frame
type Frame = () => Any

// node of a double linked list of frames
private class DoubleLinkedList(var prev: DoubleLinkedList | Null, val value: Frame, var next: DoubleLinkedList | Null):

  // push node to the front
  def push(value: Frame): DoubleLinkedList =
    assert(prev == null)
    prev = new DoubleLinkedList(null, value, this)
    prev

  // pop node from the back
  def pop(): DoubleLinkedList = 
    val tmp = prev
    if prev != null then
      prev.next = null
      prev = null
    tmp

  // attach list to tail
  def attach(dll: DoubleLinkedList): Unit =
    assert(next == null)
    next = dll
    if dll != null then
      dll.prev = this

  // detach list from tail
  def detach(): DoubleLinkedList =
    val tmp = next
    if next != null then
      next.prev = null
      next = null
    tmp

// representation of the stack
class HandledSegmentedStack:
  opaque type Handle = DoubleLinkedList

  private var first: DoubleLinkedList | Null = null
  private var last: DoubleLinkedList | Null = null

  def pushPrompt(): Handle = first

  def pushFrame(frame: Frame): Unit =
    if first == null then
      first = new DoubleLinkedList(null, frame, null)
      last = first
    else
      first = first.push(frame)

  def popFrame(): (Frame, Handle) | Null =
    if last == null then
      null
    else
      val tmp = last
      if last == first then
        first = null
        last = null
      else
        last = last.pop()
      (tmp.value, tmp)

  def splitByHandle(handle: Handle): HandledSegmentedStack =
    val res = new HandledSegmentedStack()
    if handle != null then
      if handle.prev == null then
        res.first = first
        res.last = last
        first = null
        last = null
      else
        val tmp = handle.prev
        res.first = tmp.detach()
        res.last = last
        last = tmp
    res

  def prepend(hss: HandledSegmentedStack): Unit =
    if hss.first != null then
      if first == null then
        last = hss.last
      else
        hss.last.attach(first)
      first = hss.first


  def print(): Unit =
    var tmp = first
    println("----------")
    while tmp != null do
      println(s"$tmp > ${tmp.value}")
      tmp = tmp.next
    if last != null then
      println(s"last --> $last > ${last.value}")
    println("--bottom--")
