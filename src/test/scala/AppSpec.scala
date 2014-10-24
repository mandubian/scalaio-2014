/**
  * Copyright 2014 Pascal Voitot (@mandubian)
  */
import org.scalatest._

import scalaz.{Free, Coyoneda, \/, -\/, \/-, Trampoline, ~>}

import scala.concurrent._

class AppSpec extends FlatSpec with Matchers with Instrumented {
  import shapeless._
  import ops.coproduct.{Inject, Selector}
  import Shapoyo._

  "ShapeApp" should "Strict TFree" in {
    import Free._

    // Global ADT
    sealed trait LogLevel
    case object ErrorLevel extends LogLevel
    case object WarnLevel extends LogLevel
    case object InfoLevel extends LogLevel
    case object DebugLevel extends LogLevel

    trait Log[A]
    case class LogMsg(level: LogLevel, msg: String) extends Log[Unit]


    //////////////////////////////////////////////////////////////////////////
    // DB Interaction Application
    object DB {

      // DB ADT
      type Entity = Map[String, String]

      sealed trait DBError 
      case object NotFound extends DBError

      sealed trait DBInteract[A]
      case class FindById(id: String) extends DBInteract[DBError \/ Entity]

      // APP DEFINITION
      type App[A] = DBInteract[A] :+: Log[A] :+: CNil
      type CoyoApp[A] = Coyoneda[App, A]
      type FreeApp[A] = Free.FreeC[App, A]

      // HELPERS
      object Log {
        def debug(msg: String) = Copoyo[App](LogMsg(DebugLevel, msg))
      }

      def findById(id: String): FreeApp[DBError \/ Entity] = 
        for {
          _    <- Log.debug("Searching for entity id:"+id)
          res  <- Copoyo[App](FindById(id))
          _    <- Log.debug("Search result:"+res)
        } yield (res)
    }

    //////////////////////////////////////////////////////////////////////////
    // Http Server
    object Http {

      // Http ADT
      sealed trait  HttpVerb
      case object   Get extends HttpVerb
      case object   Post extends HttpVerb

      sealed trait  HttpStatus                              { val value: Int  }
      case object   Ok                  extends HttpStatus  { val value = 200 }
      case object   BadRequest          extends HttpStatus  { val value = 400 }
      case object   InternalServerError extends HttpStatus  { val value = 500 }

      type Params = Map[String, Seq[String]]
      type Headers = Map[String, Seq[String]]

      sealed trait HttpReq {
        val verb: HttpVerb
        val url: String
        val params: Params
        val headers: Headers
      }

      case class GetReq(
        url: String,
        params: Params = Map.empty[String, Seq[String]],
        headers: Headers = Map.empty[String, Seq[String]]
      ) extends HttpReq {
        val verb = Get
      }

      case class PostReq(
        url: String,
        params: Params = Map.empty[String, Seq[String]],
        headers: Headers = Map.empty[String, Seq[String]],
        body: String
      ) extends HttpReq {
        val verb = Post
      }

      case class HttpResp (
        status: HttpStatus,
        headers: Headers = Map.empty[String, Seq[String]],
        body: String = ""
      )

      sealed trait  RecvError
      case object   ClientDisconnected extends RecvError
      case object   Timeout extends RecvError

      sealed trait  SendStatus
      case object   Ack extends SendStatus
      case object   NAck extends SendStatus

      sealed trait  HttpInteract[A]
      case object   HttpReceive extends HttpInteract[RecvError \/ HttpReq]
      case class    HttpRespond(data: HttpResp) extends HttpInteract[SendStatus]
      case class    Stop(error: RecvError \/ SendStatus) extends HttpInteract[RecvError \/ SendStatus]

      sealed trait  HttpHandle[A]
      case class    HttpHandleResult(resp: HttpResp) extends HttpHandle[HttpResp]

      // APP DEFINITION
      type App[A] = HttpInteract[A] :+: HttpHandle[A] :+: Log[A] :+: DB.FreeApp[A] :+: CNil
      type CoyoApp[A] = Coyoneda[App, A]
      type FreeApp[A] = Free.FreeC[App, A]


      // HELPERS
      def lift[F[_], A](a: F[A])(implicit inj: Inject[App[A], F[A]]): FreeApp[A] = Copoyo[App](a)

      object HttpInteract {
        def receive() = lift(HttpReceive)
        def respond(data: HttpResp) = lift(HttpRespond(data))
        def stop(err: RecvError \/ SendStatus) = lift(Stop(err))
      }

      object Log {
        def info(msg: String)       = lift(LogMsg(InfoLevel, msg))
      }

      object HttpHandle {
        def result(resp: HttpResp) = lift(HttpHandleResult(resp))
      }

      // Handle action
      def handle(req: HttpReq): FreeApp[HttpResp] = req.url match {
        case "/foo" =>
          for {
            dbRes <-  lift(DB.findById("foo"))

            resp  <-  HttpHandle.result(
                        dbRes match {
                          case -\/(err) => HttpResp(status = InternalServerError)
                          case \/-(e)   => HttpResp(status = Ok, body = e.toString)
                        }
                      ) 
          } yield (resp)

        case _ => HttpHandle.result(HttpResp(status = InternalServerError))
      }

      // Server
      def serve(): FreeApp[RecvError \/ SendStatus] =
        for {
          recv  <-  HttpInteract.receive()
          _     <-  Log.info("HttpReceived Request:"+recv)
          res   <-  recv match {
                      case -\/(err) => HttpInteract.stop(-\/(err))

                      case \/-(req) => for {
                        resp  <- handle(req)
                        _     <- Log.info("Sending Response:"+resp)
                        ack   <- HttpInteract.respond(resp)
                        res   <- if(ack == Ack) serve() else HttpInteract.stop(\/-(ack))
                      } yield (res)
                    }
        } yield (res)

    }


    //////////////////////////////////////////////////////////////////////////
    // Compile Languages

    /////////////////////////////////////////////////////////////////
    // Pure
    object Logger extends (Log ~> Id) {
      def apply[A](a: Log[A]) = a match {
        case LogMsg(lvl, msg) =>
          println(s"$lvl $msg")
      }
    }

    object DBManager extends (DB.DBInteract ~> Id) {
      def apply[A](a: DB.DBInteract[A]) = a match {
        case DB.FindById(id) =>
          println(s"DB Finding $id")
          \/-(Map("id" -> id, "name" -> "toto"))
      }
    }

    object HttpHandler extends (Http.HttpHandle ~> Id) {
      def apply[A](a: Http.HttpHandle[A]) = a match {
        case Http.HttpHandleResult(resp) =>
          println(s"Handling $resp")
          resp
      }
    }

    object HttpInteraction extends (Http.HttpInteract ~> Id) {
      var i = 0
      def apply[A](a: Http.HttpInteract[A]) = a match {
        case Http.HttpReceive       => 
          if(i < 1000) {
            i+=1
            \/-(Http.GetReq("/foo"))
          } else {
            -\/(Http.ClientDisconnected)
          }

        case Http.HttpRespond(resp) => Http.Ack

        case Http.Stop(err) => err
      }
    }

    /** let's compose NatTrans to make it stacksafe */
    object Trampolined extends (Id ~> Trampoline) {
      def apply[A](a: Id[A]) = Trampoline.done(a)
    }

    val dbInterpreter: DB.App ~> Id = DBManager ||: Logger
    val dbInterpreterCoyo: DB.CoyoApp ~> Id = liftCoyoLeft(dbInterpreter)
    val dbInterpreterFree: DB.FreeApp ~> Id = liftFree(dbInterpreterCoyo)
    
    val httpInterpreter: Http.App ~> Id = HttpInteraction ||: HttpHandler ||: Logger ||: dbInterpreterFree
    val httpInterpreterCoyo: Http.CoyoApp ~> Id = liftCoyoLeft(httpInterpreter)

    Http.serve().foldMap(Trampolined compose httpInterpreterCoyo).run

  }
}




