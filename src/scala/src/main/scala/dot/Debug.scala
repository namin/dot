package dot

trait Debug {
  val debugMode: Boolean = true
  def debug(msg: String) { if (debugMode) println(msg) }
}
