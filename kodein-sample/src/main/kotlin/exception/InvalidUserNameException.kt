package com.ynojima.kodeinsample.exception

class InvalidUserNameException(message: String, value: String)
    : ValidationException("$message: $value")
