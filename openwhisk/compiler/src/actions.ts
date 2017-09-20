
export const config = () => {
  const path = require('path')

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

  return deployConfig
}