package com.ynojima.kodeinsample.exception

import com.ynojima.kodeinsample.UserName

class DuplicatedUserNameException(message: String, userName: UserName)
    : ValidationException("$message: $userName")
