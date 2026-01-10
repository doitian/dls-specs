module Hello {
    var consoleOutput: str
    var readByUser: str

    action init = all {
        consoleOutput' = "",
        readByUser' = ""
    }

    action write = all {
        consoleOutput == "",
        consoleOutput' = "Hello, World!",
        readByUser' = readByUser
    }

    action read = all {
        consoleOutput != "",
        readByUser' = consoleOutput,
        consoleOutput' = consoleOutput
    }

    action step = any { write, read }

    run writeReadTest = init.then(write).then(read)
}