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
    stage('Build/Unit Test') {
      steps {
        sh '''
          ./scripts/build.sh
        '''
      }
      post {
        always {
          junit 'kore/test-results.xml'
        }
      }
    }
    stage('K Integration Tests') {
      steps {
        sh '''
          ./scripts/ktest.sh
        '''
      }
    }
    stage('KEVM Integration Tests') {
      when {
        anyOf {
          branch 'master'
          expression {
            TAGGED_KEVM_INTEGRATION = sh(returnStdout: true, script: './scripts/should-run-kevm-integration.sh [kevm-integration]').trim()
            return TAGGED_KEVM_INTEGRATION == 'true'
          }
        }
      }
      steps {
        sh '''
          ./scripts/kevm-integration.sh
        '''
      }
      post {
        failure {
          slackSend color: 'bad'                                                \
                  , channel: '#haskell-backend'                                 \
                  , message: "KEVM Integration Tests Failure: ${env.BUILD_URL}"
        }
      }
    }
  }
}
