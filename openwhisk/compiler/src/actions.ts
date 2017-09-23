
export const config = () => {
  const path = require('path')

  const qcertDir = path.resolve(__dirname, '..', '..', '..', '..')

  const deployConfig = {
    packages: {
      qcert: {
        actions: {
          qcertCompile: {
            location: path.resolve(qcertDir, 'bin', 'qcertJS.js')
					},
					qcert: {
						sequence: "qcert/preCompile,qcert/qcertCompile",
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