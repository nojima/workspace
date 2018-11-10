package com.ynojima.kodeinsample

data class UserId(private val value: Long) {
    fun toLong() = value
    override fun toString() = value.toString()
}
