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
          stages {

            stage('Build test runner') {
              steps {
                sh '''
                  ./scripts/kore-exec.sh
                '''
              }
            }

            stage('K') {
              options {
                timeout(time: 18, unit: 'MINUTES')
              }
              steps {
                sh '''
                  ./scripts/ktest.sh
                '''
              }
            }

            stage('KEVM') {
              when {
                anyOf {
                  branch 'master'
                  expression {
                    TAGGED_KEVM_INTEGRATION = sh(returnStdout: true, script: './scripts/should-run-kevm-integration.sh "\\[kevm-integration\\]"').trim()
                    return TAGGED_KEVM_INTEGRATION == 'true'
                  }
                }
              }
              options {
                timeout(time: 18, unit: 'MINUTES')
              }
              steps {
                sh '''
                  ./scripts/kevm-integration.sh
                '''
              }
              post {
                unsuccessful {
                  slackSend color: '#cb2431'                                            \
                          , channel: '#haskell-backend'                                 \
                          , message: "KEVM Integration Tests Failure: ${env.BUILD_URL}"
                }
              }
            }
          }
        }
      }
    }
  }
}
