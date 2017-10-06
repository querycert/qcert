## Q\*cert openWhisk service

This is code to deploy Q\*cert on the openWhisk serverless platform.

### Prerequisites

- Node.js (https://nodejs.org/en/)
- An openWhisk account (e.g., on Bluemix https://bluemix.net/)

### Building

To build the service, do:

```
make init
make compile
```

To deploy the service on openWhisk, do:

```
make deploy
```

# Thanks

Lionel Villard for his help with openwhisk-project (https://github.com/lionelvillard/openwhisk-project)
