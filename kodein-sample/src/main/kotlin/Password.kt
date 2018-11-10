package com.ynojima.kodeinsample

import com.ynojima.kodeinsample.exception.InvalidPasswordException

data class Password(private val value: String) {
    companion object {
        const val MIN_LENGTH = 6
        const val MAX_LENGTH = 128
    }

    init {
        if (value.length < MIN_LENGTH) {
            throw InvalidPasswordException("Password length must be at least $MIN_LENGTH")
        }
        if (value.length > MAX_LENGTH) {
            throw InvalidPasswordException("Password length must not exceed $MAX_LENGTH")
        }
    }

    override fun toString() = value
}
