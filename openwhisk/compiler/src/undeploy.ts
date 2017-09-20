
const undeployMain = async () => {
  try {
    const path = require('path')
    const owDeployer = require('openwhisk-deploy')

    const qcertDir = path.resolve(__dirname, '..', '..', '..', '..')

    const deployConfig = {
      packages: {
        qcert: {
          actions: {
            qcert: {
              location: path.resolve(qcertDir, 'bin', 'qcertJS.js'),
              annotations: {
                'web-export': true
              }
            }
          }
        }
      }
    }

    // Deploy
    console.log('### Deploy on OpenWhisk ###')
    const ow = owDeployer.auth.initWsk()
    try {
      await owDeployer.undeploy.apply({
        ow: ow,
        manifest: deployConfig,
        force: true
      })
    } catch (err) { }
  } catch (err) {
    console.error('Deployment failed')
    console.error(err)
    process.exit(1)
  }
}

const sleep = (time) => {
  return new Promise((resolve) => setTimeout(resolve, time))
}

undeployMain().then(() => {
  sleep(500) // XXX Hack!
}).then(() => {
  console.log('Deployment done!')
})

export { }
