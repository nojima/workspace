package example

import org.scalatest.flatspec._
import org.scalatest.matchers.should._

class HelloSpec extends AnyFlatSpec with Matchers {
  "The Hello object" should "say hello" in {
    Hello.greeting shouldEqual "hello"
  }
}
