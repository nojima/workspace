package example

import akka.{ Done, NotUsed }
import akka.actor.ActorSystem
import akka.stream._
import akka.stream.scaladsl._
import akka.util.ByteString
import scala.concurrent._
import scala.concurrent.duration._
import java.nio.file.Paths

object Hello extends App {
  implicit val system = ActorSystem("QuickStart")

  val factorials = Source(1 to 100).scan(BigInt(1))((acc, next) => acc * next)

  val result = factorials
    .zipWith(Source(0 to 100))((num, idx) => s"$idx! = $num")
    .throttle(1, 1.second)
    .runForeach(println)

  implicit val ec = system.dispatcher
  result.onComplete(_ => system.terminate())
}
