package componenttest

import TestDataSourceFactory
import com.google.common.truth.Truth.assertThat
import com.ynojima.kodeinsample.Application
import com.ynojima.kodeinsample.MainEnvironment
import TestHttpClient
import com.ynojima.kodeinsample.controller.GetUserController.GetUserResponseBody
import com.ynojima.kodeinsample.controller.SignUpController.SignUpRequestBody
import com.ynojima.kodeinsample.controller.SignUpController.SignUpResponseBody
import com.ynojima.kodeinsample.database.DatabaseOperator
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import org.kodein.di.Kodein
import org.kodein.di.generic.bind
import org.kodein.di.generic.instance
import org.kodein.di.generic.singleton
import org.kodein.di.generic.with
import org.kodein.di.newInstance
import javax.sql.DataSource

class ComponentTest {

    private val diContainer = Kodein {
        extend(MainEnvironment.diContainer)
        // ポートが被らないようにランダムポートを使うようにする
        constant(tag = "listeningPort", overrides = true) with 0
        // テスト用のMySQLを使う
        bind<DataSource>(overrides = true) with singleton { TestDataSourceFactory.create() }
    }

    private val app = Application(diContainer)
    private val databaseOperator by diContainer.newInstance { DatabaseOperator(instance()) }

    @BeforeEach
    fun initializeAndStart() {
        // データベースを初期化する
        databaseOperator.drop()
        databaseOperator.migrate()

        app.run()
    }

    @AfterEach
    fun stop() {
        app.close()
    }

    @Test
    fun createUserAndGetUser() {
        val client = TestHttpClient(app.port())

        val res1 = client.request("POST", "/users", SignUpRequestBody("Steve", "p@s5w0rD"))
        val body1: SignUpResponseBody = res1.body!!.parse()
        assertThat(body1.userName).isEqualTo("Steve")
        assertThat(res1.code).isEqualTo(200)

        val res2 = client.request("GET", "/users/${body1.userId}")
        val body2: GetUserResponseBody = res2.body!!.parse()
        assertThat(body2.userName).isEqualTo("Steve")
        assertThat(res2.code).isEqualTo(200)
    }
}
