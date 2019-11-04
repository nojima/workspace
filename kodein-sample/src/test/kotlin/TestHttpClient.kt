import com.fasterxml.jackson.core.JsonParseException
import com.fasterxml.jackson.module.kotlin.jacksonObjectMapper
import com.fasterxml.jackson.module.kotlin.readValue
import okhttp3.MediaType.Companion.toMediaType
import okhttp3.OkHttpClient
import okhttp3.Request
import okhttp3.RequestBody.Companion.toRequestBody

data class TestHttpResponseBody(val string: String) {
    companion object {
        val mapper = jacksonObjectMapper()
    }

    inline fun <reified T : Any> parse(): T {
        try {
            return mapper.readValue(string)
        } catch (e: JsonParseException) {
            throw RuntimeException("Failed to parse JSON: string='$string'", e)
        }
    }
}

data class TestHttpResponse(val code: Int, val body: TestHttpResponseBody?)

class TestHttpClient(port: Int) {
    companion object {
        private val client = OkHttpClient()
        private val mapper = jacksonObjectMapper()
    }

    private val endpoint = "http://localhost:$port"

    fun request(method: String, path: String, body: Any? = null): TestHttpResponse {
        val requestBody = body?.let {
            val json = mapper.writeValueAsString(body)
            json.toRequestBody("application/json; charset=utf-8".toMediaType())
        }
        val req = Request.Builder()
            .method(method, requestBody)
            .url("$endpoint$path")
            .build()
        return client.newCall(req).execute().use { res ->
            val responseBody = res.body?.let { TestHttpResponseBody(it.string()) }
            TestHttpResponse(res.code, responseBody)
        }
    }
}
