pipeline {
  agent {
    dockerfile {
      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  options {
    ansiColor('xterm')
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
        sh '''
          ./scripts/check.sh
        '''
      }
    }
    stage('Dependencies') {
      steps {
        sh '''
          ./scripts/clean.sh
          ./scripts/deps.sh
        '''
      }
    }
    stage('Stages') {
      failFast true
      parallel {
        stage('Documentation') {
          steps {
            sh '''
              ./scripts/docs.sh
            '''
          }
        }
        stage('Executables') {
          steps {
            sh '''
              ./scripts/kore-exec.sh
            '''
          }
        }
      }
    }
    stage('Test') {
      failFast true
      parallel {
        stage('Unit Tests') {
          steps {
            sh '''
              ./scripts/unit-test.sh
            '''
          }
          post {
            always {
              junit 'kore/test-results.xml'
            }
          }
        }
        stage('K Integration') {
          options {
            timeout(time: 16, unit: 'MINUTES')
          }
          steps {
            sh '''
              ./scripts/ktest.sh
            '''
          }
        }

        stage('KEVM Integration') {
          options {
            timeout(time: 48, unit: 'MINUTES')
          }
          steps {
            sh '''
              ./scripts/kevm-integration.sh
            '''
          }
        }
      }
    }
    stage('Update K Submodules') {
      when { branch 'master' }
      steps {
        build job: 'rv-devops/master', parameters: [string(name: 'PR_REVIEWER', value: 'ttuegel'), booleanParam(name: 'UPDATE_DEPS_K_HASKELL', value: true)], propagate: true, wait: true
      }
    }
  }
  post {
    unsuccessful {
      slackSend color: '#cb2431'                                            \
              , channel: '#haskell-backend'                                 \
              , message: "Build failure: ${env.BUILD_URL}"
    }
  }
}
