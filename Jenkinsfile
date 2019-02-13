pipeline {
  agent {
    dockerfile {
      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  stages {
    stage('Init title') {
      when { changeRequest() }
      steps {
        script {
          currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}"
        }
      }
    }
    stage('Check') {
      steps {
        ansiColor('xterm') {
          sh '''
            ./scripts/check.sh
          '''
        }
      }
    }
    stage('Build/Unit Test') {
      steps {
        ansiColor('xterm') {
          sh '''
            ./scripts/build.sh
          '''
        }
      }
    }
    stage('Build and Test') {
      parallel {
        stage('Maven') {
          steps {
            ansiColor('xterm') {
              sh '''
                mvn clean verify
              '''
            }
          }
        }
        stage('K Test') {
          steps {
            ansiColor('xterm') {
              sh '''
                ./scripts/ktest.sh
              '''
            }
          }
        }
        stage('KEVM Integration') {
          steps {
            ansiColor('xterm') {
              sh '''
                ./scripts/kevm-integration.sh
              '''
            }
          }
        }
      }
    }
  }
  post {
    always {
      junit 'src/main/haskell/kore/test-results.xml'
    }
  }
}
