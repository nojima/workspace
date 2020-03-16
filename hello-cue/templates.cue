job: [Name=string]: {
    name: Name
    replicas: uint | *1
    command: string
}

job: list: command: "ls"

job: nginx: {
    command: "nginx"
    replicas: 2
}
