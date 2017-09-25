
const deployMain = async () => {
  try {

    const owDeployer = require('openwhisk-deploy')
    const deployConfig = require('./actions').config()

    // Deploy
    console.log('### Deploy on OpenWhisk ###')
    const ow = owDeployer.auth.initWsk()
    await owDeployer.deploy({
      ow: ow,
      manifest: deployConfig,
      cache: '..',
      force: true,
      logger_level: 'INFO'
    })
  } catch (err) {
    console.error('Deployment failed')
    console.error(err)
    process.exit(1)
  }
}

const sleep = (time) => {
  return new Promise((resolve) => setTimeout(resolve, time))
}

deployMain().then(() => {
  sleep(500) // XXX Hack!
}).then(() => {
  console.log('Deployment done!')
})

export { }
