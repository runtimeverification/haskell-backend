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
  triggers {
    parameterizedCron('''
      H H * * 0 % STAGE=UPDATE-TESTS
    ''')
  }
  environment {
    LONG_REV = """${sh(returnStdout: true, script: 'git rev-parse HEAD').trim()}"""
  }
  stages {
    stage('Update regression tests') {
      when { expression { return params.STAGE == 'UPDATE-TESTS' } }
      environment {
        GITHUB_TOKEN = credentials('rv-jenkins-access-token')
      }
      steps {
        sshagent(['rv-jenkins-github']) {
          sh '''
            git clone 'ssh://github.com/kframework/kore.git' --directory kore-update-tests
            cd ../kore-update-tests
            ./../scripts/update-tests.sh
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
            build job: 'DevOps/master', propagate: false, wait: false                                   \
                , parameters: [ booleanParam ( name: 'UPDATE_DEPS'         , value: true              ) \
                              , string       ( name: 'UPDATE_DEPS_REPO'    , value: 'kframework/kore' ) \
                              , string       ( name: 'UPDATE_DEPS_VERSION' , value: "${env.LONG_REV}" ) \
                              ]
          }
        }
      }
    }
    stage('Deploy') {
      when { branch 'master' }
      stages {
        stage('GitHub Pages') {
          steps {
            sshagent(['rv-jenkins-github']) {
              dir('project-site') {
                sh '''
                  git clone 'ssh://github.com/kframework/kore.git'
                  cd kore
                  git checkout -B gh-pages origin/master
                  git submodule update --init --recursive -- ./web
                  cd web
                  npm install
                  npm run build
                  npm run build-sitemap
                  cd -
                  mv web/public_content ./
                  rm -rf $(find . -maxdepth 1 -not -name public_content -a -not -name .git -a -not -path . -a -not -path .. -a -not -name CNAME)
                  mv public_content/* ./
                  rm -rf public_content
                  git add ./
                  git commit -m 'gh-pages: Updated the website'
                  git merge --strategy ours origin/gh-pages --allow-unrelated-histories
                  git push origin gh-pages
                '''
              }
            }
          }
        }
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
