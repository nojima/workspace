import com.ynojima.kodeinsample.database.MySqlDataSourceFactory
import javax.sql.DataSource

object TestDataSourceFactory {
    fun create(): DataSource =
        MySqlDataSourceFactory.create("localhost", 3306, "kodein_sample", "root", "")
}
