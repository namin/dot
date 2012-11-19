package dot

trait Debug {
  var debugMode: Boolean = false
  def debug(msg: String) { if (debugMode) println(msg) }
  def inDebugMode[A](body: => A): A = {
    val oldDebugMode = debugMode
    debugMode = true
    try {
      body
    } finally {
      debugMode = oldDebugMode
    }
  }
}
