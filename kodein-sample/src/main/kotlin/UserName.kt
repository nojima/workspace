package com.ynojima.kodeinsample

import com.ynojima.kodeinsample.exception.InvalidUserNameException

data class UserName(private val value: String) {
    companion object {
        val pattern = Regex("[a-zA-Z0-9_]+")
    }

    init {
        if (value.isEmpty()) {
            throw InvalidUserNameException("User name must be non-empty", value)
        }
        if (!pattern.matches(value)) {
            throw InvalidUserNameException("User name must consist of alphabets, numbers, and underscores", value)
        }
    }

    override fun toString() = value
}

