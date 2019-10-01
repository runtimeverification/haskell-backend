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
    stage('Build') {
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
    stage('Integration Tests') {
      parallel {
        stage('K') {
          options {
            timeout(time: 16, unit: 'MINUTES')
          }
          steps {
            sh '''
              env KSERVER_SOCKET=${HOME:?}/.kserver-k ./scripts/integration-k.sh
            '''
          }
        }
        stage('KEVM') {
          options {
            timeout(time: 24, unit: 'MINUTES')
          }
          steps {
            sh '''
              env KSERVER_SOCKET=${HOME:?}/.kserver-kevm ./scripts/integration-kevm.sh
            '''
          }
        }
        stage('KWASM') {
          options {
            timeout(time: 8, unit: 'MINUTES')
          }
          steps {
            sh '''
              env KSERVER_SOCKET=${HOME:?}/.kserver-kwasm ./scripts/integration-kwasm.sh
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
      script {
        if (env.BRANCH_NAME == 'master') {
          slackSend color: '#cb2431'                             \
                    , channel: '#haskell-backend'                \
                    , message: "Build failure: ${env.BUILD_URL}"
        }
      }
    }
  }
}
