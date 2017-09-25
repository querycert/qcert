
const undeployMain = async () => {
  try {
    const owDeployer = require('openwhisk-deploy')

    const deployConfig = require('./actions').config()

    // Deploy
    console.log('### Undeploy OpenWhisk actions ###')
    const ow = owDeployer.auth.initWsk()
    try {
      await owDeployer.undeploy.apply({
        ow: ow,
        manifest: deployConfig,
        force: true,
        logger_level: 'INFO'
      })
    } catch (err) { }
  } catch (err) {
    console.error('Undeployment failed')
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
  console.log('Undeployment done!')
})

export { }
