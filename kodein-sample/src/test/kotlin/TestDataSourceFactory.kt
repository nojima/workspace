import com.ynojima.kodeinsample.database.MySqlDataSourceFactory
import javax.sql.DataSource

object TestDataSourceFactory {
    fun new(): DataSource =
        MySqlDataSourceFactory.new("localhost", 3306, "kodein_sample", "root", "")
}
