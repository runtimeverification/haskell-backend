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
        stage('K Integration Tests') {
          options {
            timeout(time: 18, unit: 'MINUTES')
          }
          steps {
            sh '''
              ./scripts/ktest.sh
            '''
          }
        }
        stage('KEVM Integration Tests') {
          options {
            timeout(time: 18, unit: 'MINUTES')
          }
          steps {
            sh '''
              ./scripts/kevm-integration.sh
            '''
          }
        }
      }
    }
  }
}
