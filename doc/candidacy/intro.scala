abstract class AbsCell {
  type T
  val init: T
  private var value: T = init
  def get = value
  def set(x: T) { value = x }
}
object Library {
  def reset(c: AbsCell) { c.set(c.init) }
  def update(c: AbsCell)(oldval: c.T, newval: c.T) =
    if (oldval == c.get) { c.set(newval); true }
    else false
}
