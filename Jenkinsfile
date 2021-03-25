pipeline {
  agent {
    dockerfile {
      label 'docker'
      additionalBuildArgs '--build-arg K_COMMIT=$(cat deps/k_release | cut --characters=2-) --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  parameters {
    choice(name: 'STAGE',
      choices: [
        'TEST',
        'UPDATE-TESTS'
      ],
      description: '''
        TEST: Run tests, as on push and change request events.
        UPDATE-TESTS: Update some generated tests, such as the regression tests.
      '''
    )
  }
  options {
    ansiColor('xterm')
  }
  environment {
    LONG_REV = """${sh(returnStdout: true, script: 'git rev-parse HEAD').trim()}"""
  }
  stages {
    stage('Update regression tests') {
      when { expression { return params.STAGE == 'UPDATE-TESTS' } }
      environment {
        GITHUB_TOKEN = credentials('rv-jenkins')
      }
      steps {
        sshagent(['2b3d8d6b-0855-4b59-864a-6b3ddf9c9d1a']) {
          sh '''
            git remote set-url origin git@github.com:kframework/kore
            git checkout master
            git checkout -b _update
            export KORE=$(pwd)
            ./scripts/generate-regression-tests.sh
            git add test/regression-evm test/regression-wasm
            git commit -m 'Update regression tests'
            git push -u origin _update
            hub pull-request                      \
              --head _update --base master        \
              --reviewer ttuegel --assign ttuegel \
              --labels automerge                  \
              --message 'Update regression tests'
          '''
        }
      }
    }
    stage('Test') {
      when { expression { return params.STAGE == 'TEST' } }
      stages {
        stage('Init title') {
          when { changeRequest() }
          steps {
            script {
              currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}"
            }
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
              options {
                timeout(time: 24, unit: 'MINUTES')
              }
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
              environment {
                JOBS = 2
              }
              options {
                timeout(time: 48, unit: 'MINUTES')
              }
              steps {
                sh '''
                  ./scripts/integration-k.sh
                '''
              }
            }
          }
        }
        stage('Update K Submodules') {
          when { branch 'master' }
          steps {
            build job: 'rv-devops/master', propagate: false, wait: false                                \
                , parameters: [ booleanParam ( name: 'UPDATE_DEPS'         , value: true              ) \
                              , string       ( name: 'UPDATE_DEPS_REPO'    , value: 'kframework/kore' ) \
                              , string       ( name: 'UPDATE_DEPS_VERSION' , value: "${env.LONG_REV}" ) \
                              ]
          }
        }
      }
    }
  }
  post {
    unsuccessful {
      script {
        if (env.BRANCH_NAME == 'master' || params.STAGE='UPDATE-TESTS') {
          slackSend color: '#cb2431'                             \
                    , channel: '#haskell-backend'                \
                    , message: "Build failure: ${env.BUILD_URL}"
        }
      }
    }
  }
}
